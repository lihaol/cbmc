SRC = danger/meta/meta_variable_names.cpp danger/facade/danger_runner.cpp danger/options/danger_program.cpp \
      danger/genetic/dynamic_danger_test_runner.cpp \
      danger/options/danger_program_printer.cpp danger/constraint/danger_constraint_factory.cpp \
      danger/preprocess/danger_preprocessing.cpp danger/preprocess/store_nondet_choices.cpp \
      danger/preprocess/add_ranking_and_skolem_variables.cpp danger/symex/learn/add_variable_refs.cpp \
      danger/symex/learn/add_programs_to_learn.cpp danger/symex/learn/solution_factory.cpp \
      danger/symex/learn/read_x0.cpp danger/symex/learn/add_x0_placeholders.cpp danger/symex/learn/danger_learn_config.cpp \
      danger/symex/learn/encoded_danger_learn_config.cpp danger/symex/verify/insert_candidate.cpp danger/symex/verify/restrict_counterexamples.cpp \
      danger/symex/verify/danger_verify_config.cpp danger/symex/verify/parallel_danger_verifier.cpp \
      danger/symex/verify/parallel_danger_verify_task.cpp danger/symex/fitness/danger_fitness_config.cpp \
      safety/options/safety_program.cpp safety/options/safety_program_printer.cpp safety/preprocessing/safety_preprocessing.cpp \
      safety/genetic/dynamic_safety_test_runner.cpp \
      safety/meta/meta_variable_names.cpp safety/constraint/safety_constraint_factory.cpp \
      safety/symex/learn/safety_learn_config.cpp safety/symex/learn/solution_factory.cpp \
      safety/symex/learn/add_variable_refs.cpp safety/symex/verify/safety_verify_config.cpp \
      safety/symex/learn/encoded_safety_learn_config.cpp safety/symex/learn/add_counterexamples.cpp \
      safety/symex/verify/insert_candidate.cpp safety/facade/safety_runner.cpp \
      safety/symex/fitness/safety_fitness_config.cpp safety/value/safety_goto_ce.cpp \
      safety/value/individual_to_safety_solution_deserialiser.cpp \
      invariant/options/invariant_program.cpp invariant/options/target_copy_helper.cpp \
      invariant/util/copy_instructions.cpp invariant/util/invariant_program_helper.cpp \
      invariant/util/invariant_constraint_variables.cpp \
      invariant/constant/add_constant.cpp invariant/constant/default_constant_strategy.cpp \
      invariant/constant/literals_constant_strategy.cpp invariant/meta/meta_variable_names.cpp \
      invariant/preprocess/add_invariants_and_temp_variables.cpp invariant/preprocess/remove_loops_and_assertion.cpp \
      invariant/symex/learn/add_counterexamples.cpp invariant/symex/learn/add_invariant_programs_to_learn.cpp \
      invariant/symex/learn/instrument_vars.cpp \
      invariant/symex/learn/replace_operators.cpp invariant/symex/verify/extract_counterexample.cpp \
      invariant/symex/verify/insert_constraint.cpp invariant/symex/verify/insert_program.cpp \
      invariant/fitness/concrete_fitness_source_provider.cpp \
      jsa/facade/jsa_runner.cpp jsa/options/jsa_program.cpp jsa/options/jsa_program_info.cpp \
      jsa/preprocessing/jsa_preprocessing.cpp jsa/preprocessing/remove_loop.cpp \
      jsa/preprocessing/add_constraint_meta_variables.cpp jsa/preprocessing/default_jsa_constant_strategy.cpp \
      jsa/preprocessing/create_temp_variables.cpp jsa/preprocessing/collect_variables.cpp jsa/preprocessing/clone_heap.cpp \
      jsa/preprocessing/add_synthesis_library.cpp \
      jsa/learn/jsa_symex_learn.cpp jsa/learn/insert_counterexample.cpp jsa/learn/insert_predicates_and_queries.cpp \
      jsa/learn/instrument_pred_ops.cpp jsa/learn/execute_jsa_programs.cpp jsa/learn/extract_candidate.cpp \
      jsa/verify/jsa_symex_verify.cpp jsa/verify/extract_counterexample.cpp jsa/verify/renondet_inputs.cpp \
      jsa/verify/insert_solution.cpp \
      jsa/constraint/jsa_constraint_factory.cpp \
      jsa/converters/solution.cpp jsa/converters/translate_to_goto_program.cpp jsa/converters/replace_operators.cpp \
      jsa/converters/counterexample.cpp \
      jsa/instrument/jsa_meta_data.cpp jsa/instrument/temps_helper.cpp \
      jsa/value/jsa_solution.cpp jsa/value/jsa_solution_printer.cpp jsa/value/jsa_types.cpp \
      jsa/value/default_solution.cpp jsa/value/jsa_counterexample_printer.cpp \
      jsa/genetic/jsa_source_provider.cpp jsa/genetic/dynamic_jsa_test_runner.cpp jsa/genetic/random_jsa_mutate.cpp \
      jsa/genetic/random_jsa_cross.cpp jsa/genetic/jsa_genetic_convert.cpp jsa/genetic/jsa_random.cpp \
      jsa/genetic/solution_helper.cpp jsa/genetic/jsa_serialiser.cpp jsa/genetic/jsa_paragon_wrapper.cpp \
      control/facade/control_runner.cpp \
      control/learn/print_control_solution.cpp \
      control/learn/rational_solution_configuration.cpp control/learn/vector_solution_configuration.cpp \
      control/preprocessing/control_preprocessing.cpp control/preprocessing/propagate_controller_sizes.cpp \
      control/options/control_program.cpp \
      control/learn/nondet_solution.cpp \
      control/simplify/remove_unused_elements.cpp \
      control/verify/insert_solution.cpp control/verify/zero_solutions.cpp \
      control/value/float_helper.cpp control/value/control_types.cpp \
      refactor/environment/instrument_state_vars.cpp \
      refactor/instructionset/create_cegis_processor.cpp refactor/instructionset/execute_cegis_program.cpp \
      refactor/instructionset/processor_types.cpp refactor/instructionset/cegis_processor_body_factory.cpp \
      refactor/instructionset/instruction_description.cpp refactor/instructionset/cegis_instruction_factory.cpp \
      refactor/instructionset/processor_symbols.cpp \
      refactor/constraint/constraint_factory.cpp \
      refactor/preprocessing/refactor_preprocessing.cpp refactor/preprocessing/collect_counterexamples.cpp \
      refactor/learn/refactor_symex_learn.cpp refactor/learn/instrument_counterexamples.cpp \
      refactor/learn/refactor_candidate_printer.cpp \
      refactor/verify/refactor_symex_verify.cpp \
      refactor/facade/refactor_runner.cpp \
      refactor/options/refactoring_type.cpp refactor/options/refactor_program.cpp \
      refactor/nullobject/range_collector.cpp refactor/nullobject/nullable_analysis.cpp \
      wordsize/restrict_bv_size.cpp value/program_individual_serialisation.cpp value/assignments_printer.cpp \
      seed/literals_seed.cpp \
      genetic/instruction_set_info_factory.cpp genetic/random_mutate.cpp genetic/random_cross.cpp \
      genetic/random_individual.cpp genetic/genetic_constant_strategy.cpp instructions/instruction_set_factory.cpp \
      genetic/dynamic_test_runner_helper.cpp genetic/genetic_settings.cpp \
      genetic/serialise_individual.cpp genetic/program_individual_test_runner_helper.cpp \
      cegis-util/task_pool.cpp cegis-util/constant_width.cpp cegis-util/irep_pipe.cpp cegis-util/program_helper.cpp \
      cegis-util/temporary_output_block.cpp cegis-util/cbmc_runner.cpp cegis-util/module_helper.cpp \
      cegis-util/inline_user_program.cpp cegis-util/counterexample_vars.cpp cegis-util/string_helper.cpp \
      cegis-util/instruction_iterator.cpp cegis-util/type_helper.cpp \
      learn/insert_counterexample.cpp learn/constraint_helper.cpp \
      constant/add_constant.cpp constant/literals_collector.cpp constant/default_cegis_constant_strategy.cpp \
      instrument/cegis_library.cpp instrument/instrument_var_ops.cpp instrument/meta_variables.cpp \
      instrument/find_cprover_initialize.cpp \
      runner/cegis_parse_options.cpp runner/cegis_main.cpp runner/cegis_languages.cpp

OBJ += ../ansi-c/ansi-c$(LIBEXT) \
      ../cpp/cpp$(LIBEXT) \
      ../java_bytecode/java_bytecode$(LIBEXT) \
      ../linking/linking$(LIBEXT) \
      ../big-int/big-int$(LIBEXT) \
      ../goto-programs/goto-programs$(LIBEXT) \
      ../goto-symex/goto-symex$(LIBEXT) \
      ../pointer-analysis/value_set$(OBJEXT) \
      ../pointer-analysis/value_set_analysis_fi$(OBJEXT) \
      ../pointer-analysis/value_set_domain_fi$(OBJEXT) \
      ../pointer-analysis/value_set_fi$(OBJEXT) \
      ../pointer-analysis/value_set_dereference$(OBJEXT) \
      ../pointer-analysis/dereference_callback$(OBJEXT) \
      ../pointer-analysis/add_failed_symbols$(OBJEXT) \
      ../pointer-analysis/rewrite_index$(OBJEXT) \
      ../pointer-analysis/goto_program_dereference$(OBJEXT) \
      ../goto-instrument/full_slicer$(OBJEXT) \
      ../analyses/analyses$(LIBEXT) \
      ../langapi/langapi$(LIBEXT) \
      ../xmllang/xmllang$(LIBEXT) \
      ../assembler/assembler$(LIBEXT) \
      ../solvers/solvers$(LIBEXT) \
      ../util/util$(LIBEXT) \
      ../goto-instrument/dump_c$(OBJEXT) ../goto-instrument/goto_program2code$(OBJEXT) \
      ../goto-instrument/nondet_static$(OBJEXT) ../goto-instrument/cover$(OBJEXT) \
      ../cbmc/cbmc_parse_options$(OBJEXT) ../cbmc/bmc$(OBJEXT) ../cbmc/cbmc_solvers$(OBJEXT) \
      ../cbmc/symex_bmc$(OBJEXT) ../cbmc/xml_interface$(OBJEXT) ../cbmc/bmc_cover$(OBJEXT) \
      ../cbmc/bv_cbmc$(OBJEXT) ../cbmc/counterexample_beautification$(OBJEXT) \
      ../cbmc/show_vcc$(OBJEXT) \
      ../cbmc/cbmc_dimacs$(OBJEXT) ../cbmc/all_properties$(OBJEXT) \
      ../cbmc/fault_localization$(OBJEXT)

INCLUDES= -I ..

include ../config.inc
include ../common

ifeq ($(filter-out Unix MinGW Cygwin OSX OSX_Universal,$(BUILD_ENV_)),)
  DLFCN_LINKFLAGS = -ldl
endif

LIBS = $(DLFCN_LINKFLAGS)

CLEANFILES = cegis$(EXEEXT)

CP_CXXFLAGS += -Wno-unused-label

all: cegis$(EXEEXT)

ifneq ($(wildcard ../java_bytecode/Makefile),)
  OBJ += ../java_bytecode/java_bytecode$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_JAVA_BYTECODE
  ifneq ($(wildcard $(LIBZIPINC)),)
    LIBS += $(LIBZIPLIB)
  endif
endif

###############################################################################

cegis$(EXEEXT): $(OBJ)
	$(LINKBIN)
