#ifndef _EMU_SMT2_FRONTEND_H_
#define _EMU_SMT2_FRONTEND_H_

#include <util/cmdline.h>

int smt2_frontend(const cmdlinet &);
int smt2_frontend(const cmdlinet &, std::istream &in);


#endif /*_EMU_SMT2_FRONTEND_H_*/