#include "oracle_response_parser.h"

#include <solvers/smt2/smt2_parser.h>

class smt2_expression_parsert:public smt2_parsert
{
public:
  smt2_expression_parsert(std::istream &_in) : smt2_parsert(_in)
  {
  }

  exprt expression()
  {
    return smt2_parsert::expression();
  }
};

exprt oracle_response_parser(std::istream &in)
{
  return smt2_expression_parsert(in).expression();
}
