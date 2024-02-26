use anyhow::Result;
use plonky2::field::extension::Extendable;
use plonky2::gates::constant::ConstantGate;
use plonky2::gates::gate::GateRef;
use plonky2::field::types::Field;
use plonky2::gates::noop::NoopGate;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CommonCircuitData};
use plonky2::plonk::config::{AlgebraicHasher, GenericConfig, PoseidonGoldilocksConfig};
use plonky2::recursion::cyclic_recursion::check_cyclic_proof_verifier_data;
use plonky2::recursion::dummy_circuit::cyclic_base_proof;
use std::time::SystemTime;

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
    builder.verify_proof::<C>(&proof, &verifier_data, &data.common);
    let data = builder.build::<C>();

    let config = CircuitConfig::standard_recursion_config();
    let num_consts = config.num_constants;
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let proof = builder.add_virtual_proof_with_pis(&data.common);
    let verifier_data = builder.add_virtual_verifier_data(data.common.config.fri_config.cap_height);
    builder.verify_proof::<C>(&proof, &verifier_data, &data.common);
    builder.verify_proof::<C>(&proof, &verifier_data, &data.common);
    builder.verify_proof::<C>(&proof, &verifier_data, &data.common);
    builder.add_gate_to_gate_set(GateRef::new(ConstantGate::new(num_consts)));
    builder.build::<C>().common
}

// Example Sum for PCD/IVC (output = previous_output + other_proof_output),
// The previous proof and other proof are supposed to be the same IVC circuit.
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

    let check0 = SystemTime::now();

    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);

    // Public inputs
    let initial_value = builder.add_virtual_public_input();
    let output_value = builder.add_virtual_public_input();

    // TODO: Is the return value supposed to be unused?
    let verifier_data_target = builder.add_verifier_data_public_inputs();
    
    let mut common_data = common_data_for_recursion::<F, C, D>();
    common_data.num_public_inputs = builder.num_public_inputs();
    
    let verify_proofs = builder.add_virtual_bool_target_safe();

    // Unpack inner proof's public inputs.
    let inner_cyclic_proof_with_pis = builder.add_virtual_proof_with_pis(&common_data);
    let inner_cyclic_pis = &inner_cyclic_proof_with_pis.public_inputs;
    let inner_cyclic_initial_value = inner_cyclic_pis[0];
    let inner_cyclic_output_value = inner_cyclic_pis[1];

    // Unpack other proof's public inputs.
    let other_proof_with_pis = builder.add_virtual_proof_with_pis(&common_data);
    let other_pis = &other_proof_with_pis.public_inputs;
    let _other_initial_value = other_pis[0];
    let other_output_value = other_pis[1];
    
    // Connect our initial value to that of our inner proof.
    builder.connect(initial_value, inner_cyclic_initial_value);

    // The input value is the previous output value if we have an inner proof, or the initial
    // value if this is the base case.
    // Initial value could be constrained to be 0.
    let actual_value_in = builder.select(verify_proofs, inner_cyclic_output_value, initial_value);

    let new_output_value = builder.mul_add(verify_proofs.target, other_output_value, actual_value_in);
    builder.connect(output_value, new_output_value);
    
    // Verify inner proof
    builder.conditionally_verify_cyclic_proof_or_dummy::<C>(
        verify_proofs,
        &inner_cyclic_proof_with_pis,
        &common_data,
    )?;

    // Verify other proof
    builder.conditionally_verify_cyclic_proof_or_dummy::<C>(
        verify_proofs,
        &other_proof_with_pis,
        &common_data,
    )?;

    // END OF THE CIRCUIT

    // TODO: Generate dummy proof with cyclic_base_proof
    // https://docs.rs/plonky2/0.1.4/plonky2/recursion/dummy_circuit/fn.cyclic_base_proof.html

    let cyclic_circuit_data = builder.build::<C>();
    let check1 = SystemTime::now();
    println!("Constructed Circuit Builder {}", check1.duration_since(check0).unwrap().as_secs());

    // Construct Base Proof
    let mut pw = PartialWitness::new();
    let initial_targets = [F::ZERO];
    let initial_targets_pis = initial_targets.into_iter().enumerate().collect();
    
    let initial_other_targets = [F::ZERO];
    let initial_other_targets_pis = initial_targets.into_iter().enumerate().collect();

    pw.set_bool_target(verify_proofs, false);
    pw.set_proof_with_pis_target::<C, D>(
        &inner_cyclic_proof_with_pis,
        &cyclic_base_proof(
            &common_data,
            &cyclic_circuit_data.verifier_only,
            initial_targets_pis,
        ),
    );
    pw.set_proof_with_pis_target::<C, D>(
        &other_proof_with_pis,
        &cyclic_base_proof(
            &common_data,
            &cyclic_circuit_data.verifier_only,
            initial_other_targets_pis,
        ),
    );
    pw.set_verifier_data_target(&verifier_data_target, &cyclic_circuit_data.verifier_only);
    let proof = cyclic_circuit_data.prove(pw)?;
    let check2 = SystemTime::now();
    println!("Constructed Proof, {}", check2.duration_since(check1).unwrap().as_secs());

    check_cyclic_proof_verifier_data(
        &proof,
        &cyclic_circuit_data.verifier_only,
        &cyclic_circuit_data.common,
        )?;
    cyclic_circuit_data.verify(proof.clone())?;
    let check3 = SystemTime::now();
    println!("Verified Base Proof, {}", check3.duration_since(check2).unwrap().as_secs());
    
    // Construct 1st Level Proof
    let mut pw = PartialWitness::new();
    pw.set_bool_target(verify_proofs, true);
    pw.set_proof_with_pis_target::<C, D>(&inner_cyclic_proof_with_pis, &proof);
    pw.set_proof_with_pis_target::<C, D>(&other_proof_with_pis, &proof);
    pw.set_verifier_data_target(&verifier_data_target, &cyclic_circuit_data.verifier_only);
    let proof = cyclic_circuit_data.prove(pw)?;
    let check4 = SystemTime::now();
    println!("Constructed Proof, {}", check4.duration_since(check3).unwrap().as_secs());

    check_cyclic_proof_verifier_data(
        &proof,
        &cyclic_circuit_data.verifier_only,
        &cyclic_circuit_data.common,
        )?;
    cyclic_circuit_data.verify(proof.clone())?;
    let check5 = SystemTime::now();
    println!("Verifier 1st Layer Proof, {}", check5.duration_since(check4).unwrap().as_secs());

    Ok(())
}
