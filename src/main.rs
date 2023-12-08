use anyhow::Result;
use plonky2::field::extension::Extendable;
use plonky2::field::types::Field;
use plonky2::gates::noop::NoopGate;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CommonCircuitData};
use plonky2::plonk::config::{AlgebraicHasher, GenericConfig, PoseidonGoldilocksConfig};
use plonky2::recursion::cyclic_recursion::check_cyclic_proof_verifier_data;
use plonky2::recursion::dummy_circuit::cyclic_base_proof;

// Useful example hash chain test: https://docs.rs/plonky2/latest/src/plonky2/recursion/cyclic_recursion.rs.html#1-354

// Generates `CommonCircuitData` usable for recursion.
fn common_data_for_recursion<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
>() -> CommonCircuitData<F, D>
where
    C::Hasher: AlgebraicHasher<F>,
{
    let config = CircuitConfig::standard_recursion_config();
    let builder = CircuitBuilder::<F, D>::new(config);
    let data = builder.build::<C>();
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let proof = builder.add_virtual_proof_with_pis(&data.common);
    let verifier_data = builder.add_virtual_verifier_data(data.common.config.fri_config.cap_height);
    builder.verify_proof::<C>(&proof, &verifier_data, &data.common);
    let data = builder.build::<C>();

    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let proof = builder.add_virtual_proof_with_pis(&data.common);
    let verifier_data = builder.add_virtual_verifier_data(data.common.config.fri_config.cap_height);
    builder.verify_proof::<C>(&proof, &verifier_data, &data.common);
    while builder.num_gates() < 1 << 12 {
        builder.add_gate(NoopGate, vec![]);
    }
    builder.build::<C>().common
}

// Example Sum of two proofs added to an IVC chain (output = previous_output + other_proof_1_output +
// other_proof_2_output)
// Layout:
// - initial value
// - output value
//
// Condition:
// - verify_proofs (boolean)
fn main() -> Result<()> {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);

    // Public inputs
    let initial_value = builder.add_virtual_public_input();
    let output_value = builder.add_virtual_public_input();

    let mut common_data = common_data_for_recursion::<F, C, D>();

    let verify_proofs = builder.add_virtual_bool_target_safe();

    let verifier_data_target = builder.add_verifier_data_public_inputs();
    common_data.num_public_inputs = builder.num_public_inputs();

    // Unpack inner proof's public inputs.
    let inner_cyclic_proof_with_pis = builder.add_virtual_proof_with_pis(&common_data);
    let inner_cyclic_pis = &inner_cyclic_proof_with_pis.public_inputs;
    let inner_cyclic_initial_value = inner_cyclic_pis[0];
    let inner_cyclic_output_value = inner_cyclic_pis[1];

    // Connect our initial value to that of our inner proof. (If there is no inner proof, the
    // initial value will be unconstrained, which is intentional.)
    builder.connect(initial_value, inner_cyclic_initial_value);

    // The input value is the previous output value if we have an inner proof, or the initial
    // value if this is the base case.
    let actual_value_in = builder.select(verify_proofs, inner_cyclic_output_value, initial_value);

    // Unpack first proof's public inputs.
    let p1_proof_with_pis = builder.add_virtual_proof_with_pis(&common_data);
    let p1_pis = &p1_proof_with_pis.public_inputs;
    // In a real setting we would have some rules for the initial_value, e.g. they
    // are generated from a global state. For this it might be necessary to have them
    // as public inputs for later verification.
    let _p1_initial_value = p1_pis[0];
    let p1_output_value = p1_pis[1];

    // Unpack second proof's public inputs.
    let p2_proof_with_pis = builder.add_virtual_proof_with_pis(&common_data);
    let p2_pis = &p2_proof_with_pis.public_inputs;
    let _p2_initial_value = p2_pis[0];
    let p2_output_value = p2_pis[1];

    let proofs_sum = builder.add(p1_output_value, p2_output_value);
    let new_output_value = builder.mul_add(verify_proofs.target, proofs_sum, actual_value_in);
    builder.connect(output_value, new_output_value);
    
    // Verify inner proof
    builder.conditionally_verify_cyclic_proof_or_dummy::<C>(
        verify_proofs,
        &inner_cyclic_proof_with_pis,
        &common_data,
    )?;

    // Verify proof 1
    builder.conditionally_verify_cyclic_proof_or_dummy::<C>(
        verify_proofs,
        &p1_proof_with_pis,
        &common_data,
    )?;

    // Verify proof 2
    builder.conditionally_verify_cyclic_proof_or_dummy::<C>(
        verify_proofs,
        &p2_proof_with_pis,
        &common_data,
    )?;

    // END OF THE CIRCUIT

    // TODO: Generate dummy proof with cyclic_base_proof
    // https://docs.rs/plonky2/0.1.4/plonky2/recursion/dummy_circuit/fn.cyclic_base_proof.html

    let cyclic_circuit_data = builder.build::<C>();

    // IVC
    // first initial proof with recursively verifying a dummy proof
    let mut pw = PartialWitness::new();
    let initial_targets = [Field::ONE];
    //let initial_targets_pis = initial_targets.into_iter().enumerate().collect();
    pw.set_bool_target(verify_proofs, false);
    pw.set_proof_with_pis_target::<C, D>(
        &inner_cyclic_proof_with_pis,
        &cyclic_base_proof(
            &common_data,
            &cyclic_circuit_data.verifier_only,
            initial_targets.into_iter().enumerate().collect(),
        ),
    );
    //pw.set_proof_with_pis_target::<C, D>(
    //    &p1_proof_with_pis,
    //    &cyclic_base_proof(
    //        &common_data,
    //        &cyclic_circuit_data.verifier_only,
    //        initial_targets.into_iter().enumerate().collect(),
    //    ),
    //);
    //pw.set_proof_with_pis_target::<C, D>(
    //    &p1_proof_with_pis,
    //    &cyclic_base_proof(
    //        &common_data,
    //        &cyclic_circuit_data.verifier_only,
    //        initial_targets.into_iter().enumerate().collect(),
    //    ),
    //);
    pw.set_verifier_data_target(&verifier_data_target, &cyclic_circuit_data.verifier_only);
    let proof = cyclic_circuit_data.prove(pw)?;
    check_cyclic_proof_verifier_data(
        &proof,
        &cyclic_circuit_data.verifier_only,
        &cyclic_circuit_data.common,
    )?;
    cyclic_circuit_data.verify(proof.clone())?;
    println!(
        "Initial value: {}\nOutput: {}",
        proof.public_inputs[0], proof.public_inputs[1]
    );

    // 1st recursive layer.
    //let mut pw = PartialWitness::new();
    //pw.set_proof_with_pis_target(&inner_cyclic_proof_with_pis, &proof);
    //pw.set_bool_target(verify_proofs, true);
    //pw.set_verifier_data_target(&verifier_data_target, &cyclic_circuit_data.verifier_only);
    //let proof = cyclic_circuit_data.prove(pw)?;
    //check_cyclic_proof_verifier_data(
    //    &proof,
    //    &cyclic_circuit_data.verifier_only,
    //    &cyclic_circuit_data.common,
    //)?;
    //cyclic_circuit_data.verify(proof.clone())?;
    //println!(
    //    "Initial value: {}\nOutput: {}",
    //    proof.public_inputs[0], proof.public_inputs[1]
    //);

    //// 2nd recursive layer.
    //let mut pw = PartialWitness::new();
    //pw.set_proof_with_pis_target(&inner_cyclic_proof_with_pis, &proof);
    //pw.set_bool_target(verify_proofs, true);
    //pw.set_verifier_data_target(&verifier_data_target, &cyclic_circuit_data.verifier_only);
    //let proof = cyclic_circuit_data.prove(pw)?;
    //check_cyclic_proof_verifier_data(
    //    &proof,
    //    &cyclic_circuit_data.verifier_only,
    //    &cyclic_circuit_data.common,
    //)?;
    //println!(
    //    "Initial value: {}\nOutput: {}",
    //    proof.public_inputs[0], proof.public_inputs[1]
    //);
    cyclic_circuit_data.verify(proof)
}
