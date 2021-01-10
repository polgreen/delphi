#include "oracle_response_parser.h"

#include <solvers/smt2/smt2_parser.h>

class smt2_model_parsert:public smt2_parsert
{
public:
  smt2_model_parsert(std::istream &_in) : smt2_parsert(_in)
  {
  }

  std::map<symbol_exprt, exprt> model();
};

std::map<symbol_exprt, exprt> smt2_model_parsert::model()
{
  // ( (define-fun x () Int 8) (define-fun y () Int 6) )
  if(next_token() != smt2_tokenizert::OPEN)
    throw error("expected '('");

  std::map<symbol_exprt, exprt> result;

  while(smt2_tokenizer.peek() == smt2_tokenizert::OPEN)
  {
    next_token(); // eat '('

    if(next_token() != smt2_tokenizert::SYMBOL)
      throw error("expected symbol in model");

    if(smt2_tokenizer.get_buffer() == "define-fun")
    {
      // get identifier
      if(next_token() != smt2_tokenizert::SYMBOL)
        throw error("expected identifier in define-fun");

      auto identifier = smt2_tokenizer.get_buffer();
      const auto signature = function_signature_definition();
      const auto body = expression();

      // store
      auto symbol = symbol_exprt(identifier, body.type());
      result[symbol] = body;
    }
    else
      throw error() << smt2_tokenizer.get_buffer() << " unexpected in model";

    if(next_token() != smt2_tokenizert::CLOSE)
      throw error("expected ')' at end of define-fun");    
  }

  if(next_token() != smt2_tokenizert::CLOSE)
    throw error("expected ')' at end of model");

  return result;
}

std::map<symbol_exprt, exprt> oracle_response_parser(std::istream &in)
{
  return smt2_model_parsert(in).model();
}
