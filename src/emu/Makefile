SRC = emu_main.cpp expr2sygus.cpp ogis.cpp sygus_parser.cpp sygus_frontend.cpp \
synthesis/simple_synth.cpp synthesis/synth_encoding.cpp smt2_frontend.cpp \
verification/oracle_interface.cpp \
verification/oracle_solver.cpp \
verification/oracle_response_parser.cpp \
synthesis/synthesizer.cpp verification/verify_encoding.cpp literals.cpp

OBJ+= ../../$(CPROVER_DIR)/src/ansi-c/ansi-c$(LIBEXT) \
      ../../$(CPROVER_DIR)/src/assembler/assembler$(LIBEXT) \
      ../../$(CPROVER_DIR)/src/linking/linking$(LIBEXT) \
      ../../$(CPROVER_DIR)/src/big-int/big-int$(LIBEXT) \
      ../../$(CPROVER_DIR)/src/goto-symex/goto-symex$(LIBEXT) \
      ../../$(CPROVER_DIR)/src/goto-programs/goto-programs$(LIBEXT) \
      ../../$(CPROVER_DIR)/src/pointer-analysis/pointer-analysis$(LIBEXT) \
      ../../$(CPROVER_DIR)/src/analyses/analyses$(LIBEXT) \
      ../../$(CPROVER_DIR)/src/langapi/langapi$(LIBEXT) \
      ../../$(CPROVER_DIR)/src/solvers/solvers$(LIBEXT) \
      ../../$(CPROVER_DIR)/src/analyses/dirty$(OBJEXT) \
      ../../$(CPROVER_DIR)/src/util/util$(LIBEXT)

INCLUDES= -I ../../$(CPROVER_DIR)/src -I ..

LIBS =

include ../config.inc
include ../../$(CPROVER_DIR)/src/config.inc
include ../../$(CPROVER_DIR)/src/common

CLEANFILES = fastsynth$(EXEEXT)

all: emu$(EXEEXT)

###############################################################################

emu$(EXEEXT): $(OBJ)
	$(LINKBIN)
