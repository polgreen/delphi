#ifndef EMU_ORACLE_INTERFACE_H_
#define EMU_ORACLE_INTERFACE_H_

#include "verify.h"

class oracle_interfacet:public verifyt
{
  protected:
  // initialisation

  
  /// Namespace passed on to decision procedure.

  // snthesis encoding

 public: 
  resultt operator()( problemt &problem,
    const std::function<exprt(exprt)> &model) override;


  /// program size

};

#endif /* EMU_ORACLE_INTERFACE_H_ */

