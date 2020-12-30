#include "oracle_interface.h"

  oracle_interfacet::resultt oracle_interfacet::operator()( problemt &problem,
    const std::function<exprt(exprt)> &model)
    {
        return oracle_interfacet::resultt::FAIL;
    }