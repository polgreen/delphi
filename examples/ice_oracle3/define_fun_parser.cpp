#include "define_fun_parser.h"

#include <solvers/smt2/smt2_parser.h>
#include <solvers/smt2/smt2_format.h>
#include <iostream>

class smt2_define_fun_parsert:public smt2_parsert
{
public:
  smt2_define_fun_parsert(std::istream &_in) : smt2_parsert(_in)
  {
  }

  void replace_local_var(exprt &expr, const irep_idt &target, exprt &replacement)
  {
    if (expr.id() == ID_symbol)
    {
      if (to_symbol_expr(expr).get_identifier() == target)
        expr = replacement;
    }
    for (auto &op : expr.operands())
      replace_local_var(op, target, replacement);
  }

  void expand_let_expressions(exprt &expr)
  {
    if (expr.id() == ID_let)
    {
      auto &let_expr = to_let_expr(expr);
      for (unsigned int i = 0; i < let_expr.variables().size(); i++)
      {
        INVARIANT(let_expr.variables()[i].id() == ID_symbol,
                  "Let expression should have list of symbols, not " + let_expr.variables()[i].pretty());
        replace_local_var(let_expr.where(), to_symbol_expr(let_expr.variables()[i]).get_identifier(), let_expr.values()[i]);
      }
      expr = let_expr.where();
      expand_let_expressions(expr);
    }
    for (auto &op : expr.operands())
      expand_let_expressions(op);
  }

  define_fun_resultt define_fun()
  {
    if(next_token() != smt2_tokenizert::OPEN)
    {
      throw error("expected (define-fun");
    }

    if(next_token() != smt2_tokenizert::SYMBOL ||
       smt2_tokenizer.get_buffer() != "define-fun")
      throw error("expected (define-fun");

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
    expand_let_expressions(result.body);

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
    // eat the ')'
    next_token();
    return result;
  }

  std::map<irep_idt, exprt> model_parser()
  {
    std::map<irep_idt, exprt> result;
    if (next_token() != smt2_tokenizert::OPEN)
      throw error("expected model");

    if(smt2_tokenizer.peek() == smt2_tokenizert::SYMBOL)
      if(smt2_tokenizer.get_buffer() != "model")
        throw error("expected model, got different buffer");

    while(smt2_tokenizer.peek() != smt2_tokenizert::CLOSE)
    {
      define_fun_resultt tmpresult = define_fun();
      result[tmpresult.id]=tmpresult.body;
    }
    // eat the ')'
    next_token();

    return result;
  }
};

std::map<irep_idt, exprt> model_parser(std::istream &in)
{
  return smt2_define_fun_parsert(in).model_parser();
}

define_fun_resultt define_fun_parser(std::istream &in)
{
  return smt2_define_fun_parsert(in).define_fun();
}
