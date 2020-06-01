#ifndef EMU_SYNTHESIZER_H
#define EMU_SYNTHESIZER_H

#include <functional>
#include <util/expr.h>

class synthesizert
{
public:
  exprt operator()(const std::function<exprt(exprt)> &model);
};

#endif /*EMU_SYNTHESIZER_H*/