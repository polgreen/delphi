#ifndef EMU_SIMPLE_SYNTH_H_
#define EMU_SIMPLE_SYNTH_H_

#include "synthesizer.h"
#include "synth_encoding.h"

class simple_syntht:public synthesizert
{
  protected:
  // initialisation

  
  /// Namespace passed on to decision procedure.

  // snthesis encoding
  synth_encodingt synth_encoding;

 public: 
  resultt operator()(const problemt &) override;

  exprt model(exprt) const override;

  /// program size

};

#endif /* EMU_SIMPLE_SYNTH_H_ */

