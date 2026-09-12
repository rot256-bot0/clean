import Witgen.Backends.CaliperRuntimeGuide


/-! Exact public compiler, writer, example and runtime-guide theorem inventory.
The Python harness independently pins this list and checks every axiom report. -/

-- Caliper
#print axioms Witgen.Backends.Caliper.compile_inputs_fresh
#print axioms Witgen.Backends.Caliper.decode_add
#print axioms Witgen.Backends.Caliper.decode_mul
#print axioms Witgen.Backends.Caliper.decode_div
#print axioms Witgen.Backends.Caliper.decode_mod
#print axioms Witgen.Backends.Caliper.compileWord_correct
#print axioms Witgen.Backends.Caliper.read_env
#print axioms Witgen.Backends.Caliper.locSchema_respects
#print axioms Witgen.Backends.Caliper.compileStruct_correct
#print axioms Witgen.Backends.Caliper.compileList_correct
#print axioms Witgen.Backends.Caliper.compileAggregate_correct
#print axioms Witgen.Backends.Caliper.quadratic_compiles
#print axioms Witgen.Backends.Caliper.modMul_compiles
#print axioms Witgen.Backends.Caliper.quadratic_code
#print axioms Witgen.Backends.Caliper.modMul_code
#print axioms Witgen.Backends.Caliper.quadratic_result
#print axioms Witgen.Backends.Caliper.modMul_result
#print axioms Witgen.Backends.Caliper.quadraticWord_eval_u64
#print axioms Witgen.Backends.Caliper.quadratic_run
#print axioms Witgen.Backends.Caliper.modMul_run
#print axioms Witgen.Backends.Caliper.fixedGated_compiles
#print axioms Witgen.Backends.Caliper.fixedGated_result
#print axioms Witgen.Backends.Caliper.fixedGatedWord_eval
#print axioms Witgen.Backends.Caliper.fixedGated_run
#print axioms Witgen.Backends.Caliper.exec_of_observed_run
#print axioms Witgen.Backends.Caliper.compileWord_frame
#print axioms Witgen.Backends.Caliper.quadratic_frame
#print axioms Witgen.Backends.Caliper.modMul_frame
#print axioms Witgen.Backends.Caliper.fixedGated_frame
#print axioms Witgen.Backends.Caliper.quadratic_exec
#print axioms Witgen.Backends.Caliper.modMul_exec
#print axioms Witgen.Backends.Caliper.fixedGated_exec

-- CaliperWitness
#print axioms Witgen.Backends.CaliperWitness.pushState_regs
#print axioms Witgen.Backends.CaliperWitness.pushState_caps
#print axioms Witgen.Backends.CaliperWitness.pushState_tapePos
#print axioms Witgen.Backends.CaliperWitness.pushState_other
#print axioms Witgen.Backends.CaliperWitness.pushState_contents
#print axioms Witgen.Backends.CaliperWitness.pushRegs_exec
#print axioms Witgen.Backends.CaliperWitness.writeRegs_exec
#print axioms Witgen.Backends.CaliperWitness.writerState_regs
#print axioms Witgen.Backends.CaliperWitness.writerState_tapePos
#print axioms Witgen.Backends.CaliperWitness.writerState_contents
#print axioms Witgen.Backends.CaliperWitness.writerState_capacity
#print axioms Witgen.Backends.CaliperWitness.writerState_other
#print axioms Witgen.Backends.CaliperWitness.writerState_post
#print axioms Witgen.Backends.CaliperWitness.writeRegs_triple
#print axioms Witgen.Backends.CaliperWitness.writerTime_unit
#print axioms Witgen.Backends.CaliperWitness.writerTime_cycles
#print axioms Witgen.Backends.CaliperWitness.writeRegs_unique
#print axioms Witgen.Backends.CaliperWitness.pushRegs_noWrites
#print axioms Witgen.Backends.CaliperWitness.writeRegs_noWrites
#print axioms Witgen.Backends.CaliperWitness.pushRegs_touches
#print axioms Witgen.Backends.CaliperWitness.writeRegs_touches
#print axioms Witgen.Backends.CaliperWitness.writeRegs_liveMem
#print axioms Witgen.Backends.CaliperWitness.writeRegs_reaches_bound
#print axioms Witgen.Backends.CaliperWitness.produce_write_exec
#print axioms Witgen.Backends.CaliperWitness.reserved_load_noExec
#print axioms Witgen.Backends.CaliperWitness.full_push_noExec

-- CaliperExamples
#print axioms Witgen.Backends.CaliperExamples.quadratic_producer_exec
#print axioms Witgen.Backends.CaliperExamples.modMul_producer_exec
#print axioms Witgen.Backends.CaliperExamples.withWitness_exec
#print axioms Witgen.Backends.CaliperExamples.quadratic_witness_exec
#print axioms Witgen.Backends.CaliperExamples.modMul_witness_exec
#print axioms Witgen.Backends.CaliperExamples.quadratic_triple
#print axioms Witgen.Backends.CaliperExamples.modMul_triple
#print axioms Witgen.Backends.CaliperExamples.quadratic_unit_cost
#print axioms Witgen.Backends.CaliperExamples.quadratic_cycles_cost
#print axioms Witgen.Backends.CaliperExamples.modMul_unit_cost
#print axioms Witgen.Backends.CaliperExamples.modMul_cycles_cost
#print axioms Witgen.Backends.CaliperExamples.quadratic_unit_resources
#print axioms Witgen.Backends.CaliperExamples.modMul_unit_resources
#print axioms Witgen.Backends.CaliperExamples.quadratic_cells_circuit
#print axioms Witgen.Backends.CaliperExamples.modMul_cells_circuit
#print axioms Witgen.Backends.CaliperExamples.quadratic_circuit_exec
#print axioms Witgen.Backends.CaliperExamples.modMul_circuit_exec
#print axioms Witgen.Backends.CaliperExamples.quadList_regs_read
#print axioms Witgen.Backends.CaliperExamples.fixedGated_witness_exec
#print axioms Witgen.Backends.CaliperExamples.fixedGated_unit_triple
#print axioms Witgen.Backends.CaliperExamples.fixedGated_unit_cost
#print axioms Witgen.Backends.CaliperExamples.fixedGated_cycles_cost
#print axioms Witgen.Backends.CaliperExamples.fixedGated_cycles_triple
#print axioms Witgen.Backends.CaliperExamples.compiled_register_endpoints
#print axioms Witgen.Backends.CaliperExamples.quadratic_intermediate_memory
#print axioms Witgen.Backends.CaliperExamples.modMul_intermediate_memory

-- CaliperRuntimeGuide
#print axioms Witgen.Backends.CaliperRuntimeGuide.quadratic_runtime
#print axioms Witgen.Backends.CaliperRuntimeGuide.quadratic_exact_cost
#print axioms Witgen.Backends.CaliperRuntimeGuide.modMul_runtime
#print axioms Witgen.Backends.CaliperRuntimeGuide.modMul_exact_cost
