#include "define_fun_parser.h"

#include <solvers/smt2/smt2_parser.h>
#include <solvers/smt2/smt2_format.h>

class smt2_define_fun_parsert:public smt2_parsert
{
public:
  smt2_define_fun_parsert(std::istream &_in) : smt2_parsert(_in)
  {
  }

  define_fun_resultt define_fun()
  {
    if(next_token() != smt2_tokenizert::SYMBOL)
      throw error("expected a symbol after define-fun");

    // save the renaming map
    renaming_mapt old_renaming_map = renaming_map;

    define_fun_resultt result;

    result.id = smt2_tokenizer.get_buffer();

    const auto signature = function_signature_definition();
    result.type = signature.type;
    result.parameters = signature.parameters;
    result.body = expression();

    // restore renamings
    std::swap(renaming_map, old_renaming_map);

    // check type of body
    if(signature.type.id() == ID_mathematical_function)
    {
      const auto &f_signature = to_mathematical_function_type(signature.type);
      if(result.body.type() != f_signature.codomain())
      {
        throw error() << "type mismatch in function definition: expected '"
                      << smt2_format(f_signature.codomain()) << "' but got '"
                      << smt2_format(result.body.type()) << '\'';
      }
    }
    else if(result.body.type() != signature.type)
    {
      throw error() << "type mismatch in function definition: expected '"
                    << smt2_format(signature.type) << "' but got '"
                    << smt2_format(result.body.type()) << '\'';
    }

    return result;
  }
};

define_fun_resultt define_fun_parser(std::istream &in)
{
  return smt2_define_fun_parsert(in).define_fun();
}
