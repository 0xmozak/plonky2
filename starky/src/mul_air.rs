use alloc::vec::Vec;
use core::marker::PhantomData;

use log::debug;
use plonky2::field::extension::{Extendable, FieldExtension};
use plonky2::field::packed::PackedField;
use plonky2::field::polynomial::PolynomialValues;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::ext_target::ExtensionTarget;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use rand::{thread_rng, Rng};

use crate::constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer};
use crate::evaluation_frame::{StarkEvaluationFrame, StarkFrame};
use crate::stark::Stark;
use crate::util::trace_rows_to_poly_values;

/// How many `a * b = c` operations to do per row in the AIR.
const REPETITIONS: usize = 911;
const TRACE_WIDTH: usize = REPETITIONS * 3;

#[derive(Copy, Clone)]
struct MulAirStark<F: RichField + Extendable<D>, const D: usize> {
    num_rows: usize,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> MulAirStark<F, D> {
    const fn new(num_rows: usize) -> Self {
        Self {
            num_rows,
            _phantom: PhantomData,
        }
    }

    fn generate_trace(&self) -> Vec<PolynomialValues<F>> {
        let mut rng = thread_rng();
        let mut trace_rows = Vec::with_capacity(self.num_rows);
        for _ in 0..self.num_rows {
            let mut row: [F; REPETITIONS * 3] = [F::ZERO; REPETITIONS * 3];
            for i in 0..REPETITIONS {
                row[i * 3] = F::from_canonical_u64(rng.gen::<u64>());
                row[i * 3 + 1] = F::from_canonical_u64(rng.gen::<u64>());
                row[i * 3 + 2] = row[i * 3] * row[i * 3 + 1];
            }
            trace_rows.push(row);
        }
        debug!(
            "trace height: {}, trace width: {}",
            trace_rows.len(),
            trace_rows[0].len()
        );

        trace_rows_to_poly_values(trace_rows)
    }
}

const COLUMNS: usize = TRACE_WIDTH;
const PUBLIC_INPUTS: usize = 0;

impl<F: RichField + Extendable<D>, const D: usize> Stark<F, D> for MulAirStark<F, D> {
    type EvaluationFrame<FE, P, const D2: usize> = StarkFrame<P, P::Scalar, COLUMNS, PUBLIC_INPUTS>
        where
            FE: FieldExtension<D2, BaseField = F>,
            P: PackedField<Scalar = FE>;

    type EvaluationFrameTarget =
        StarkFrame<ExtensionTarget<D>, ExtensionTarget<D>, COLUMNS, PUBLIC_INPUTS>;

    fn eval_packed_generic<FE, P, const D2: usize>(
        &self,
        vars: &Self::EvaluationFrame<FE, P, D2>,
        yield_constr: &mut ConstraintConsumer<P>,
    ) where
        FE: FieldExtension<D2, BaseField = F>,
        P: PackedField<Scalar = FE>,
    {
        let local_values = vars.get_local_values();

        for i in 0..REPETITIONS {
            yield_constr.constraint_transition(
                local_values[i * 3 + 2] - local_values[i * 3] * local_values[i * 3 + 1],
            );
        }
    }

    fn eval_ext_circuit(
        &self,
        _builder: &mut CircuitBuilder<F, D>,
        _vars: &Self::EvaluationFrameTarget,
        _yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    ) {
        unimplemented!()
    }

    fn constraint_degree(&self) -> usize {
        2
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;
    use log::{debug, Level};
    use plonky2::plonk::config::{GenericConfig, Poseidon2GoldilocksConfig};
    use plonky2::util::timing::TimingTree;

    use crate::config::StarkConfig;
    use crate::mul_air::MulAirStark;
    use crate::prover::prove;
    use crate::verifier::verify_stark_proof;

    #[test]
    fn test_mulair_stark() -> Result<()> {
        init_logger();

        const D: usize = 2;
        type C = Poseidon2GoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        type S = MulAirStark<F, D>;

        let mut config = StarkConfig::standard_fast_config();
        config.fri_config.num_query_rounds = 100;
        let num_rows = 1 << 14;
        let public_inputs = [];
        let stark = S::new(num_rows);
        let trace = stark.generate_trace();
        let mut timing = TimingTree::new("prove mul air stark", Level::Debug);
        let proof = prove::<F, C, S, D>(stark, &config, trace, &public_inputs, &mut timing)?;
        timing.print();
        let serialized_proof = postcard::to_allocvec(&proof).expect("unable to serialize proof");

        debug!("serialized_proof len: {} bytes", serialized_proof.len());

        verify_stark_proof(stark, proof, &config)
    }

    fn init_logger() {
        let _ = env_logger::builder().format_timestamp(None).try_init();
    }
}
