SRC = implication_query.cpp define_fun_parser.cpp ../expr2sygus.cpp ../sygus_parser.cpp

OBJ+= ../../../$(CPROVER_DIR)/src/ansi-c/ansi-c$(LIBEXT) \
      ../../../$(CPROVER_DIR)/src/assembler/assembler$(LIBEXT) \
      ../../../$(CPROVER_DIR)/src/linking/linking$(LIBEXT) \
      ../../../$(CPROVER_DIR)/src/big-int/big-int$(LIBEXT) \
      ../../../$(CPROVER_DIR)/src/goto-symex/goto-symex$(LIBEXT) \
      ../../../$(CPROVER_DIR)/src/goto-programs/goto-programs$(LIBEXT) \
      ../../../$(CPROVER_DIR)/src/pointer-analysis/pointer-analysis$(LIBEXT) \
      ../../../$(CPROVER_DIR)/src/analyses/analyses$(LIBEXT) \
      ../../../$(CPROVER_DIR)/src/langapi/langapi$(LIBEXT) \
      ../../../$(CPROVER_DIR)/src/solvers/solvers$(LIBEXT) \
      ../../../$(CPROVER_DIR)/src/analyses/dirty$(OBJEXT) \
      ../../../$(CPROVER_DIR)/src/util/util$(LIBEXT)


INCLUDES= -I ../../$(CPROVER_DIR)/src -I ../.. -I ..

LIBS =

include ../../config.inc
include ../../../$(CPROVER_DIR)/src/config.inc
include ../../../$(CPROVER_DIR)/src/common

CLEANFILES = iceoracle$(EXEEXT)

all: iceoracle$(EXEEXT)

###############################################################################

iceoracle$(EXEEXT): $(OBJ)
	$(LINKBIN)