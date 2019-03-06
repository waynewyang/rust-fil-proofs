use std::marker::PhantomData;

use bellman::{Circuit, ConstraintSystem, SynthesisError};
use pairing::bls12_381::{Bls12, Fr};
use sapling_crypto::circuit::num;
use sapling_crypto::jubjub::JubjubEngine;

use crate::circuit::constraint;
use crate::circuit::drgporep::{ComponentPrivateInputs, DrgPoRepCompound};
use crate::circuit::pedersen::pedersen_md_no_padding;
use crate::circuit::variables::Root;
use crate::compound_proof::{CircuitComponent, CompoundProof};
use crate::drgporep::{self, DrgPoRep};
use crate::drgraph::{graph_height, Graph};
use crate::hasher::{Domain, Hasher};
use crate::layered_drgporep::{self, Layers as LayersTrait};
use crate::parameter_cache::{CacheableParameters, ParameterSetIdentifier};
use crate::porep;
use crate::proof::ProofScheme;
use crate::util::bytes_into_boolean_vec;
use crate::zigzag_drgporep::ZigZagDrgPoRep;

type Layers<'a, H, G> = Vec<
    Option<(
        <DrgPoRep<'a, H, G> as ProofScheme<'a>>::PublicInputs,
        <DrgPoRep<'a, H, G> as ProofScheme<'a>>::Proof,
    )>,
>;

/// ZigZag DRG based Proof of Replication.
///
/// # Fields
///
/// * `params` - parameters for the curve
/// * `public_params` - ZigZagDrgPoRep public parameters.
/// * 'layers' - A vector of Layers – each representing a DrgPoRep proof (see Layers type definition).
///
pub struct ZigZagCircuit<'a, E: JubjubEngine, H: 'static + Hasher> {
    params: &'a E::Params,
    public_params: <ZigZagDrgPoRep<'a, H> as ProofScheme<'a>>::PublicParams,
    layers: Layers<
        'a,
        <ZigZagDrgPoRep<'a, H> as LayersTrait>::Hasher,
        <ZigZagDrgPoRep<'a, H> as LayersTrait>::Graph,
    >,
    tau: Option<porep::Tau<<<ZigZagDrgPoRep<'a, H> as LayersTrait>::Hasher as Hasher>::Domain>>,
    comm_r_star: Option<H::Domain>,
    _e: PhantomData<E>,
}

impl<'a, E: JubjubEngine, H: Hasher> CircuitComponent for ZigZagCircuit<'a, E, H> {
    type ComponentPrivateInputs = ();
}

impl<'a, H: Hasher> ZigZagCircuit<'a, Bls12, H> {
    pub fn synthesize<CS>(
        mut cs: CS,
        params: &'a <Bls12 as JubjubEngine>::Params,
        public_params: <ZigZagDrgPoRep<'a, H> as ProofScheme<'a>>::PublicParams,
        layers: Layers<
            'a,
            <ZigZagDrgPoRep<H> as LayersTrait>::Hasher,
            <ZigZagDrgPoRep<H> as LayersTrait>::Graph,
        >,
        tau: Option<porep::Tau<<<ZigZagDrgPoRep<H> as LayersTrait>::Hasher as Hasher>::Domain>>,
        comm_r_star: Option<H::Domain>,
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<Bls12>,
    {
        let circuit = ZigZagCircuit::<'a, Bls12, H> {
            params,
            public_params,
            layers,
            tau,
            comm_r_star,
            _e: PhantomData,
        };

        circuit.synthesize(&mut cs)
    }
}

impl<'a, H: Hasher> Circuit<Bls12> for ZigZagCircuit<'a, Bls12, H> {
    fn synthesize<CS: ConstraintSystem<Bls12>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        let graph = &self.public_params.graph;
        let layer_challenges = &self.public_params.layer_challenges;
        let sloth_iter = self.public_params.sloth_iter;

        let mut crs_input = vec![0u8; 32 * (self.layers.len() + 1)];

        assert_eq!(layer_challenges.layers(), self.layers.len());

        if let Some(ref l) = self.layers[0] {
            l.0.replica_id
                .write_bytes(&mut crs_input[0..32])
                .expect("failed to write vec");
        }

        let public_comm_d =
            num::AllocatedNum::alloc(cs.namespace(|| "public comm_d value"), || {
                let opt: Option<_> = self.tau.map(|t| t.comm_d.into());
                opt.ok_or_else(|| SynthesisError::AssignmentMissing)
            })?;

        public_comm_d.inputize(cs.namespace(|| "zigzag comm_d"))?;

        let public_comm_r =
            num::AllocatedNum::alloc(cs.namespace(|| "public comm_r value"), || {
                let opt: Option<_> = self.tau.map(|t| t.comm_r.into());
                opt.ok_or_else(|| SynthesisError::AssignmentMissing)
            })?;

        public_comm_r.inputize(cs.namespace(|| "zigzag comm_r"))?;

        // Yuck. This will never be used, but we need an initial value to satisfy the compiler.
        let mut previous_comm_r_var = Root::Val(self.tau.map(|t| t.comm_d.into()));

        dbg!(self.layers.len());
        for (l, v) in self.layers.iter().enumerate() {
            dbg!(l);
            let public_inputs = v.as_ref().map(|v| &v.0);
            let layer_proof = v.as_ref().map(|v| &v.1);
            dbg!(public_inputs.is_some());
            dbg!(layer_proof.is_some());

            let is_first_layer = l == 0;
            let is_last_layer = l == self.layers.len() - 1;

            let height = graph_height(graph.size());
            let proof = match layer_proof {
                Some(wrapped_proof) => {
                    let typed_proof: drgporep::Proof<<ZigZagDrgPoRep<H> as LayersTrait>::Hasher> =
                        wrapped_proof.into();
                    typed_proof
                }
                // Synthesize a default drgporep if none is supplied – for use in tests, etc.
                None => drgporep::Proof::new_empty(
                    height,
                    graph.degree(),
                    layer_challenges.challenges_for_layer(l),
                ),
            };
            dbg!("after proof");
            let comm_r = proof.replica_root;

            let comm_d_var = if is_first_layer {
                Root::Var(public_comm_d.clone())
            } else {
                previous_comm_r_var
            };

            let comm_r_var = if is_last_layer {
                Root::Var(public_comm_r.clone())
            } else {
                Root::var(
                    &mut cs.namespace(|| format!("layer {} comm_r", l)),
                    comm_r.into(),
                )
            };
            previous_comm_r_var = comm_r_var.clone();

            dbg!("write commr");
            comm_r
                .write_bytes(&mut crs_input[(l + 1) * 32..(l + 2) * 32])
                .expect("failed to write vec");

            // TODO: As an optimization, we may be able to skip proving the original data
            // on some (50%?) of challenges.

            let porep_params = drgporep::PublicParams::new(
                graph.clone(), // TODO: avoid
                sloth_iter,
                true,
                layer_challenges.challenges_for_layer(l),
            );
            let circuit = if let Some(public_inputs) = public_inputs {
                dbg!("regular");
                DrgPoRepCompound::circuit(
                    &public_inputs,
                    ComponentPrivateInputs {
                        comm_d: Some(comm_d_var),
                        comm_r: Some(comm_r_var),
                    },
                    &proof,
                    &porep_params,
                    self.params,
                )
            } else {
                dbg!("blank");
                DrgPoRepCompound::blank_circuit(&porep_params, &self.params)
            };
            dbg!("synthesize porep");
            circuit.synthesize(&mut cs.namespace(|| format!("zigzag layer {}", l)))?;
        }

        println!("after loop");

        let crs_boolean = bytes_into_boolean_vec(
            cs.namespace(|| "comm_r_star boolean"),
            Some(&crs_input),
            8 * crs_input.len(),
        )?;

        let computed_comm_r_star =
            pedersen_md_no_padding(cs.namespace(|| "comm_r_star"), self.params, &crs_boolean)?;

        let public_comm_r_star =
            num::AllocatedNum::alloc(cs.namespace(|| "public comm_r_star value"), || {
                self.comm_r_star
                    .ok_or_else(|| SynthesisError::AssignmentMissing)
                    .map(Into::into)
            })?;

        constraint::equal(
            cs,
            || "enforce comm_r_star is correct",
            &computed_comm_r_star,
            &public_comm_r_star,
        );

        public_comm_r_star.inputize(cs.namespace(|| "zigzag comm_r_star"))?;

        println!("zigzag synth done");

        Ok(())
    }
}

#[allow(dead_code)]
pub struct ZigZagCompound {
    partitions: Option<usize>,
}

impl<E: JubjubEngine, C: Circuit<E>, P: ParameterSetIdentifier> CacheableParameters<E, C, P>
    for ZigZagCompound
{
    fn cache_prefix() -> String {
        String::from("zigzag-proof-of-replication")
    }
}

impl<'a, H: 'static + Hasher>
    CompoundProof<'a, Bls12, ZigZagDrgPoRep<'a, H>, ZigZagCircuit<'a, Bls12, H>>
    for ZigZagCompound
{
    fn generate_public_inputs(
        pub_in: &<ZigZagDrgPoRep<H> as ProofScheme>::PublicInputs,
        pub_params: &<ZigZagDrgPoRep<H> as ProofScheme>::PublicParams,
        k: Option<usize>,
    ) -> Vec<Fr> {
        let mut inputs = Vec::new();

        let comm_d = pub_in.tau.expect("missing tau").comm_d.into();
        inputs.push(comm_d);

        let comm_r = pub_in.tau.expect("missing tau").comm_r.into();
        inputs.push(comm_r);

        let mut current_graph = Some(pub_params.graph.clone());

        for layer in 0..pub_params.layer_challenges.layers() {
            let drgporep_pub_params = drgporep::PublicParams::new(
                current_graph.take().unwrap(),
                pub_params.sloth_iter,
                true,
                pub_params.layer_challenges.challenges_for_layer(layer),
            );

            let drgporep_pub_inputs = drgporep::PublicInputs {
                replica_id: pub_in.replica_id,
                challenges: pub_in.challenges(
                    &pub_params.layer_challenges,
                    pub_params.graph.size(),
                    layer as u8,
                    k,
                ),
                tau: None,
            };

            let drgporep_inputs = DrgPoRepCompound::generate_public_inputs(
                &drgporep_pub_inputs,
                &drgporep_pub_params,
                None,
            );
            inputs.extend(drgporep_inputs);

            current_graph = Some(<ZigZagDrgPoRep<H> as layered_drgporep::Layers>::transform(
                &drgporep_pub_params.graph,
            ));
        }
        inputs.push(pub_in.comm_r_star.into());
        inputs
    }

    fn circuit<'b>(
        public_inputs: &'b <ZigZagDrgPoRep<H> as ProofScheme>::PublicInputs,
        _component_private_inputs: <ZigZagCircuit<'a, Bls12, H> as CircuitComponent>::ComponentPrivateInputs,
        vanilla_proof: &'b <ZigZagDrgPoRep<H> as ProofScheme>::Proof,
        public_params: &'b <ZigZagDrgPoRep<H> as ProofScheme>::PublicParams,
        engine_params: &'a <Bls12 as JubjubEngine>::Params,
    ) -> ZigZagCircuit<'a, Bls12, H> {
        let layers = (0..(vanilla_proof.encoding_proofs.len()))
            .map(|l| {
                let layer_public_inputs = drgporep::PublicInputs {
                    replica_id: public_inputs.replica_id,
                    // Challenges are not used in circuit synthesis. Don't bother generating.
                    challenges: vec![],
                    tau: None,
                };
                let layer_proof = vanilla_proof.encoding_proofs[l].clone();
                Some((layer_public_inputs, layer_proof))
            })
            .collect();

        let pp: <ZigZagDrgPoRep<H> as ProofScheme>::PublicParams = public_params.into();

        ZigZagCircuit {
            params: engine_params,
            public_params: pp,
            tau: public_inputs.tau,
            comm_r_star: Some(public_inputs.comm_r_star),
            layers,
            _e: PhantomData,
        }
    }

    fn blank_circuit(
        public_params: &<ZigZagDrgPoRep<H> as ProofScheme>::PublicParams,
        params: &'a <Bls12 as JubjubEngine>::Params,
    ) -> ZigZagCircuit<'a, Bls12, H> {
        let layers = vec![None; public_params.layer_challenges.layers()];
        let pp: <ZigZagDrgPoRep<H> as ProofScheme>::PublicParams = public_params.into();

        ZigZagCircuit {
            params,
            public_params: pp,
            tau: None,
            comm_r_star: None,
            layers,
            _e: PhantomData,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::test::*;
    use crate::compound_proof;
    use crate::drgporep;
    use crate::drgraph::new_seed;
    use crate::fr32::fr_into_bytes;
    use crate::hasher::pedersen::*;
    use crate::layered_drgporep::{self, LayerChallenges};
    use crate::porep::PoRep;
    use crate::proof::ProofScheme;
    use crate::zigzag_graph::{ZigZag, ZigZagGraph};

    use pairing::Field;
    use rand::{Rng, SeedableRng, XorShiftRng};
    use sapling_crypto::jubjub::JubjubBls12;

    #[test]
    fn zigzag_drgporep_input_circuit_with_bls12_381() {
        let params = &JubjubBls12::new();
        let nodes = 5;
        let degree = 1;
        let expansion_degree = 2;
        let num_layers = 2;
        let layer_challenges = LayerChallenges::new_fixed(num_layers, 1);
        let sloth_iter = 1;

        let n = nodes; // FIXME: Consolidate variable names.

        // TODO: The code in this section was copied directly from zizag_drgporep::tests::prove_verify.
        // We should refactor to share the code – ideally in such a way that we can just add
        // methods and get the assembled tests for free.
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let replica_id: Fr = rng.gen();
        let data: Vec<u8> = (0..n)
            .flat_map(|_| fr_into_bytes::<Bls12>(&rng.gen()))
            .collect();
        // create a copy, so we can compare roundtrips
        let mut data_copy = data.clone();
        let sp = layered_drgporep::SetupParams {
            drg: drgporep::DrgParams {
                nodes: n,
                degree,
                expansion_degree,
                seed: new_seed(),
            },
            sloth_iter,
            layer_challenges: layer_challenges.clone(),
        };

        let pp = ZigZagDrgPoRep::setup(&sp).unwrap();
        let (tau, aux) =
            ZigZagDrgPoRep::replicate(&pp, &replica_id.into(), data_copy.as_mut_slice(), None)
                .unwrap();
        assert_ne!(data, data_copy);

        let simplified_tau = tau.clone().simplify();

        let pub_inputs = layered_drgporep::PublicInputs::<PedersenDomain> {
            replica_id: replica_id.into(),
            tau: Some(tau.simplify().into()),
            comm_r_star: tau.comm_r_star.into(),
            k: None,
        };

        let priv_inputs = layered_drgporep::PrivateInputs::<PedersenHasher> {
            aux: aux.into(),
            tau: tau.layer_taus.into(),
        };

        let proofs =
            ZigZagDrgPoRep::prove_all_partitions(&pp, &pub_inputs, &priv_inputs, 1).unwrap();
        assert!(ZigZagDrgPoRep::verify_all_partitions(&pp, &pub_inputs, &proofs).unwrap());

        // End copied section.

        let mut cs = TestConstraintSystem::<Bls12>::new();

        ZigZagCompound::circuit(
            &pub_inputs,
            <ZigZagCircuit<Bls12, PedersenHasher> as CircuitComponent>::ComponentPrivateInputs::default(),
            &proofs[0],
            &pp,
            params,
        )
        .synthesize(&mut cs.namespace(|| "zigzag drgporep"))
        .expect("failed to synthesize circuit");

        if !cs.is_satisfied() {
            println!(
                "failed to satisfy: {:?}",
                cs.which_is_unsatisfied().unwrap()
            );
        }

        assert!(cs.is_satisfied(), "constraints not satisfied");
        assert_eq!(cs.num_inputs(), 16, "wrong number of inputs");
        assert_eq!(cs.num_constraints(), 131097, "wrong number of constraints");

        assert_eq!(cs.get_input(0, "ONE"), Fr::one());

        assert_eq!(
            cs.get_input(1, "zigzag drgporep/zigzag comm_d/input variable"),
            simplified_tau.comm_d.into(),
        );

        assert_eq!(
            cs.get_input(2, "zigzag drgporep/zigzag comm_r/input variable"),
            simplified_tau.comm_r.into(),
        );

        assert_eq!(
            cs.get_input(3, "zigzag drgporep/zigzag layer 0/replica_id/input 0"),
            replica_id.into(),
        );

        // This test was modeled on equivalent from drgporep circuit.
        // TODO: add add assertions about other inputs.
    }

    #[test]
    fn zigzag_input_circuit_num_constraints_fixed() {
        let params = &JubjubBls12::new();
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        // 1 GB
        let n = (1 << 30) / 32;
        let num_layers = 2;
        let base_degree = 2;
        let expansion_degree = 2;
        let layer_challenges = LayerChallenges::new_fixed(num_layers, 1);
        let sloth_iter = 2;
        let challenge = 1;
        let replica_id: Fr = rng.gen();

        let mut cs = TestConstraintSystem::<Bls12>::new();
        let graph = ZigZagGraph::new_zigzag(n, base_degree, expansion_degree, new_seed());
        let height = graph.merkle_tree_depth() as usize;

        let layers = (0..num_layers)
            .map(|l| {
                // l is ignored because we assume uniform layers here.
                let public_inputs = drgporep::PublicInputs {
                    replica_id: replica_id.into(),
                    challenges: vec![challenge],
                    tau: None,
                };
                let proof = drgporep::Proof::new_empty(
                    height,
                    graph.degree(),
                    layer_challenges.challenges_for_layer(l),
                );
                Some((public_inputs, proof))
            })
            .collect();
        let public_params =
            layered_drgporep::PublicParams::new(graph, sloth_iter, layer_challenges);

        ZigZagCircuit::<Bls12, PedersenHasher>::synthesize(
            cs.namespace(|| "zigzag_drgporep"),
            params,
            public_params,
            layers,
            Some(porep::Tau {
                comm_r: rng.gen(),
                comm_d: rng.gen(),
            }),
            rng.gen(),
        )
        .expect("failed to synthesize circuit");
        assert!(cs.is_satisfied(), "TestContraintSystem was not satisfied");

        assert_eq!(cs.num_inputs(), 18, "wrong number of inputs");
        assert_eq!(cs.num_constraints(), 547539, "wrong number of constraints");
    }

    #[test]
    fn zigzag_input_circuit_num_constraints_tapered() {
        let params = &JubjubBls12::new();
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let n = (1024 * 1024) / 32;
        let num_layers = 2;
        let base_degree = 2;
        let expansion_degree = 2;
        let layer_challenges = LayerChallenges::new_tapered(num_layers, 3, 2, 1.0 / 3.0);
        let sloth_iter = 2;
        let challenge = 1;
        let replica_id: Fr = rng.gen();

        let mut cs = TestConstraintSystem::<Bls12>::new();
        let graph = ZigZagGraph::new_zigzag(n, base_degree, expansion_degree, new_seed());
        let height = graph.merkle_tree_depth() as usize;

        let layers = (0..num_layers)
            .map(|l| {
                // l is ignored because we assume uniform layers here.
                let public_inputs = drgporep::PublicInputs {
                    replica_id: replica_id.into(),
                    challenges: vec![challenge; layer_challenges.challenges_for_layer(l)],
                    tau: None,
                };
                let proof = drgporep::Proof::new_empty(
                    height,
                    graph.degree(),
                    layer_challenges.challenges_for_layer(l),
                );
                Some((public_inputs, proof))
            })
            .collect();
        let public_params =
            layered_drgporep::PublicParams::new(graph, sloth_iter, layer_challenges);

        ZigZagCircuit::<Bls12, PedersenHasher>::synthesize(
            cs.namespace(|| "zigzag_drgporep"),
            params,
            public_params,
            layers,
            Some(porep::Tau {
                comm_r: rng.gen(),
                comm_d: rng.gen(),
            }),
            rng.gen(),
        )
        .expect("failed to synthesize circuit");
        assert!(cs.is_satisfied(), "TestContraintSystem was not satisfied");

        assert_eq!(cs.num_inputs(), 18, "wrong number of inputs");
        assert_eq!(cs.num_constraints(), 547539, "wrong number of constraints");
    }

    #[test]
    #[ignore] // Slow test – run only when compiled for release.
    fn zigzag_test_compound() {
        let params = &JubjubBls12::new();
        let nodes = 5;
        let degree = 2;
        let expansion_degree = 1;
        let num_layers = 4;
        let layer_challenges = LayerChallenges::new_tapered(num_layers, 4, num_layers, 1.0 / 3.0);
        let sloth_iter = 1;
        let partition_count = 1;

        let n = nodes; // FIXME: Consolidate variable names.

        // TODO: The code in this section was copied directly from zizag_drgporep::tests::prove_verify.
        // We should refactor to share the code – ideally in such a way that we can just add
        // methods and get the assembled tests for free.
        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let replica_id: Fr = rng.gen();
        let data: Vec<u8> = (0..n)
            .flat_map(|_| fr_into_bytes::<Bls12>(&rng.gen()))
            .collect();
        // create a copy, so we can compare roundtrips
        let mut data_copy = data.clone();

        let setup_params = compound_proof::SetupParams {
            engine_params: params,
            vanilla_params: &layered_drgporep::SetupParams {
                drg: drgporep::DrgParams {
                    nodes: n,
                    degree,
                    expansion_degree,
                    seed: new_seed(),
                },
                sloth_iter,
                layer_challenges: layer_challenges.clone(),
            },
            partitions: Some(partition_count),
        };

        let public_params = ZigZagCompound::setup(&setup_params).unwrap();
        let (tau, aux) = ZigZagDrgPoRep::replicate(
            &public_params.vanilla_params,
            &replica_id.into(),
            data_copy.as_mut_slice(),
            None,
        )
        .unwrap();
        assert_ne!(data, data_copy);

        let public_inputs = layered_drgporep::PublicInputs::<PedersenDomain> {
            replica_id: replica_id.into(),
            tau: Some(tau.simplify()),
            comm_r_star: tau.comm_r_star,
            k: None,
        };
        let private_inputs = layered_drgporep::PrivateInputs::<PedersenHasher> {
            aux,
            tau: tau.layer_taus,
        };

        // TOOD: Move this to e.g. circuit::test::compound_helper and share between all compound proofs.
        {
            let (circuit, inputs) =
                ZigZagCompound::circuit_for_test(&public_params, &public_inputs, &private_inputs);

            let mut cs = TestConstraintSystem::new();

            circuit.synthesize(&mut cs).expect("failed to synthesize");

            assert!(cs.is_satisfied(), "TestContraintSystem was not satisfied");
            assert!(
                cs.verify(&inputs),
                "verification failed with TestContraintSystem and generated inputs"
            );
        }

        let blank_groth_params =
            ZigZagCompound::groth_params(&public_params.vanilla_params, params).unwrap();

        let proof = ZigZagCompound::prove(
            &public_params,
            &public_inputs,
            &private_inputs,
            &blank_groth_params,
        )
        .expect("failed while proving");

        let verified = ZigZagCompound::verify(&public_params, &public_inputs, &proof)
            .expect("failed while verifying");

        assert!(verified);
    }
}
