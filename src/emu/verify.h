#ifndef EMU_VERIFY_H
#define EMU_VERIFY_H

#include <functional>
#include <util/expr.h>

class verifyt
{
public:
  exprt operator()(const std::function<exprt(exprt)> &model);
};

#endif /*EMU_VERIFY_H*/