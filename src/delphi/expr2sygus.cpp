#include "expr2sygus.h"

#include <util/mathematical_expr.h>
#include <util/mathematical_types.h>
#include <util/arith_tools.h>

// TODO: add operators for non-bitvectors
std::string type2sygus(const typet &type)
{
  std::string result;
  if (type.id() == ID_unsignedbv)
  {
    result += "(_ BitVec " + integer2string(to_unsignedbv_type(type).get_width()) + ")";
  }
  else if (type.id() == ID_integer)
  {
    result += "Int";
  }
  else if (type.id() == ID_bool)
  {
    result += "Bool";
  }
  else if (type.id() == ID_array)
  {
    array_typet array = to_array_type(type);
    result += "(Array " + type2sygus(array.size().type()) + " " + type2sygus(array.subtype()) + ")";
  }
  else if (type.id()==ID_mathematical_function)
  {
    result +="(-> ";
    for (const auto &t: to_mathematical_function_type(type).domain())
      result += type2sygus(t)+ " ";
    result += type2sygus(to_mathematical_function_type(type).codomain());
    result+=")";
  }
  else
  {
    std::cout << "Unhandled type " << type.pretty() << std::endl;
    assert(0);
  }
  return result;
}

std::string clean_id(const irep_idt &id)
{
  std::string dest = id2string(id);
  std::string::size_type c_pos = dest.find("#");
  if (c_pos != std::string::npos &&
      dest.rfind("#") == c_pos)
    dest.erase(c_pos, std::string::npos);

  std::string::size_type c_pos2 = dest.find("synth::"); //7 chars
  if (c_pos2 != std::string::npos &&
      dest.rfind("synth::") == c_pos2)
    dest.erase(0, c_pos2 + 7);

  return dest;
}

void clean_symbols(exprt &expr)
{
  for (auto &op : expr.operands())
    clean_symbols(op);

  if (expr.id() == ID_symbol)
  {
    std::string new_id = clean_id(to_symbol_expr(expr).get_identifier());
    std::string::size_type c_pos = new_id.find("parameter");

    if (c_pos != std::string::npos &&
        new_id.rfind("parameter") == c_pos)
      new_id = "synth::" + new_id;
    {
      to_symbol_expr(expr).set_identifier(new_id);
      return;
    }
  }
}

std::string expr2sygus_var_dec(const symbol_exprt &symbol)
{
  std::string result ="(declare-fun ";
  result += id2string(symbol.get_identifier()) + " () " + type2sygus(symbol.type()) + ")\n";
  return result;
}

std::string expr2sygus_fun_def(const symbol_exprt &function, const exprt&body)
{
  INVARIANT(function.type().id()==ID_mathematical_function, "unsupported function definition type");
  std::string result = "(define-fun " + clean_id(function.get_identifier()) + " (";
  const auto &func_type = to_mathematical_function_type(function.type());

  for(std::size_t i=0; i<func_type.domain().size(); i++)
  {
    result+="( parameter"+ integer2string(i, 10u) +" "+type2sygus(func_type.domain()[i]) + ")"; 
  }
  result +=")\n " + type2sygus(func_type.codomain()) + " " + expr2sygus(body) + ")\n";
  return result;
}

std::string expr2sygus_fun_dec(const symbol_exprt &function)
{
  INVARIANT(function.type().id()==ID_mathematical_function, "unsupported function definition type");
  std::string result = "(declare-fun " + clean_id(function.get_identifier()) + " (";
  const auto &func_type = to_mathematical_function_type(function.type());

  for(std::size_t i=0; i<func_type.domain().size(); i++)
  {
    result+= type2sygus(func_type.domain()[i]) + " "; 
  }
  result +=")\n " + type2sygus(func_type.codomain()) +  ")\n";
  return result;
}

std::string synth_fun_dec(const irep_idt &id, const synth_functiont &definition)
{
  INVARIANT(definition.type.id()==ID_mathematical_function, "unsupported function definition type");
  std::string result = "(synth-fun " + clean_id(id) + " (";
  const auto &func_type = to_mathematical_function_type(definition.type);

  for(std::size_t i=0; i<definition.parameters.size(); i++)
  {
    result+="(" + clean_id(definition.parameters[i]) + " "+type2sygus(func_type.domain()[i]) + ")"; 
  }
  result +=")\n " + type2sygus(func_type.codomain()) + "\n";

  std::string nts = "(";
  std::string rules = "(";
  // declare nonterminals
  for(int i=0; i< definition.grammar.nt_ids.size(); i++)
  {
    auto &nt = definition.grammar.nt_ids[i];
    auto &rule = definition.grammar.production_rules.at(nt);
    nts += "(" + id2string(nt) + " " + type2sygus(rule[0].type()) + ")";
    rules +="( " + id2string(nt) + " " + type2sygus(rule[0].type()) + "(";
    for(const auto &r: rule)
     rules += expr2sygus(r) + " ";
    rules +="))\n";
  }
  nts+=")\n";
  rules +=")\n";
  result += nts + rules + ")\n";
  return result;
}


std::string synth_fun_dec(const symbol_exprt &function, std::string grammar)
{
  INVARIANT(function.type().id()==ID_mathematical_function, "unsupported function definition type");
  std::string result = "(synth-fun " + clean_id(function.get_identifier()) + " (";
  const auto &func_type = to_mathematical_function_type(function.type());

  for(std::size_t i=0; i<func_type.domain().size(); i++)
  {
    result+="( parameter"+ integer2string(i, 10u) +" "+type2sygus(func_type.domain()[i]) + ")"; 
  }
  result +=")\n " + type2sygus(func_type.codomain()) + "\n" + grammar +  ")\n";
  return result;
}


std::string expr2sygus(const exprt &expr)
{
  std::string result = "(";

  if (expr.id() == ID_equal)
    result += "= " + expr2sygus(expr.operands()[0]) + " " +
              expr2sygus(expr.operands()[1]);
  else if(expr.id()==ID_notequal)
  {
    result += "not (= " + expr2sygus(expr.operands()[0]) + " " +
              expr2sygus(expr.operands()[1])+")";

  }            
  else if (expr.id() == ID_le)
  {
    bool use_integers = expr.operands()[0].type().id()==ID_integer;
    bool use_signed=expr.operands()[0].type().id()==ID_signedbv;
    if (use_signed)
    {
      result += (use_integers ? "<= " : "bvsle ") + expr2sygus(expr.operands()[0]) + " " +
                expr2sygus(expr.operands()[1]);
    }
    else
      result += (use_integers ? "<= " : "bvule ") + expr2sygus(expr.operands()[0]) + " " +
                expr2sygus(expr.operands()[1]);
  }
  else if (expr.id() == ID_ge)
  {
    bool use_integers = expr.operands()[0].type().id()==ID_integer;
    bool use_signed=expr.operands()[0].type().id()==ID_signedbv;
    if (use_signed)
      result += (use_integers ? ">= " : "bvsge ") + expr2sygus(expr.operands()[0]) + " " +
                expr2sygus(expr.operands()[1]);
    else
      result += (use_integers ? ">= " : "bvuge ") + expr2sygus(expr.operands()[0]) + " " +
                expr2sygus(expr.operands()[1]);
  }
  else if (expr.id() == ID_lt)
  {
    bool use_integers = expr.operands()[0].type().id()==ID_integer;
    bool use_signed=expr.operands()[0].type().id()==ID_signedbv;
    if (use_signed)
      result += (use_integers ? "< " : "bvslt ") + expr2sygus(expr.operands()[0]) + " " +
                expr2sygus(expr.operands()[1]);
    else
      result += (use_integers ? "< " : "bvult ") + expr2sygus(expr.operands()[0]) + " " +
                expr2sygus(expr.operands()[1]);
  }
  else if (expr.id() == ID_gt)
  {
    bool use_integers = expr.operands()[0].type().id()==ID_integer;
    bool use_signed=expr.operands()[0].type().id()==ID_signedbv;
    if (use_signed)
      result += (use_integers ? "> " : "bvsgt ") + expr2sygus(expr.operands()[0]) + " " +
                expr2sygus(expr.operands()[1]);
    else
      result += (use_integers ? "> " : "bvugt ") + expr2sygus(expr.operands()[0]) + " " +
                expr2sygus(expr.operands()[1]);
  }
  else if(expr.id()==ID_mod || expr.id()==ID_rem)
  {
    INVARIANT(expr.type().id()!=ID_integer, "cannot use mod with integer types in sygus");
    result += "bvurem "+ expr2sygus(expr.operands()[0]) + " "+ expr2sygus(expr.operands()[1]);
  }
  else if (expr.id() == ID_and)
  {
    result += "and";
    for (const auto &op : expr.operands())
      result += " " + expr2sygus(op);
  }
  else if (expr.id() == ID_or)
  {
    result += "or";
    for (const auto &op : expr.operands())
      result += " " + expr2sygus(op) ;
  }
  else if (expr.id() == ID_xor)
    result += "xor " + expr2sygus(expr.operands()[0]) + " " +
              expr2sygus(expr.operands()[1]);
  else if (expr.id() == ID_not)
    result += "not " + expr2sygus(expr.operands()[0]);

  else if (expr.id() == ID_bitand)
    result += "bvand " + expr2sygus(expr.operands()[0]) + " " +
              expr2sygus(expr.operands()[1]);
  else if (expr.id() == ID_bitor)
    result += "bvor " + expr2sygus(expr.operands()[0]) + " " +
              expr2sygus(expr.operands()[1]);
  else if (expr.id() == ID_bitxor)
    result += "bvxor " + expr2sygus(expr.operands()[0]) + " " +
              expr2sygus(expr.operands()[1]);
  else if (expr.id() == ID_bitxnor)
    result += "bvxnor " + expr2sygus(expr.operands()[0]) + " " +
              expr2sygus(expr.operands()[1]);
  else if (expr.id() == ID_bitnot)
    result += "bvnot " + expr2sygus(expr.operands()[0]);
  else if (expr.id() == ID_lshr)
    result += "bvlshr " + expr2sygus(expr.operands()[0]) + " " +
              expr2sygus(expr.operands()[1]);
  else if (expr.id() == ID_ashr)
    result += "bvashr " + expr2sygus(expr.operands()[0]) + " " +
              expr2sygus(expr.operands()[1]);
  else if (expr.id() == ID_shl)
    result += "bvlshl " + expr2sygus(expr.operands()[0]) + " " +
              expr2sygus(expr.operands()[1]);
  else if (expr.id() == ID_unary_minus)
  {
    if (expr.type().id()==ID_integer)
      return result = "(- " + expr2sygus(expr.operands()[0]) + ")";
    else
      result += "bvneg " + expr2sygus(expr.operands()[0]);
  }
  else if (expr.id() == ID_plus)
  {
    result += ((expr.type().id()==ID_integer) ? "+" : "bvadd");
    for (const auto &op : expr.operands())
      result += " " + expr2sygus(op);
  }
  else if (expr.id() == ID_minus)
  {
    result += ((expr.type().id()==ID_integer) ? "- "
                              : "bvsub ") +
                expr2sygus(expr.operands()[0]) +
                " " + expr2sygus(expr.operands()[1]);
  }
  else if (expr.id() == ID_mult)
    result += ((expr.type().id()==ID_integer) ? "* " : "bvmul ") + expr2sygus(expr.operands()[0]) + " " +
              expr2sygus(expr.operands()[1]);
  else if (expr.id() == ID_implies)
  {
    result += "=> " + expr2sygus(expr.operands()[0]) + " " + expr2sygus(expr.operands()[1]);
  }
  else if (expr.id() == ID_function_application)
  {
    function_application_exprt fapp = to_function_application_expr(expr);
    if (fapp.function().id() != ID_symbol)
    {
      std::cout << "Unsupported function application " << expr.pretty() << std::endl;
      assert(0);
    }
    result += clean_id(to_symbol_expr(fapp.function()).get_identifier());
    for (const auto &arg : fapp.arguments())
      result += " " + expr2sygus(arg);
  }
  else if (expr.id() == ID_symbol)
  {
    return result = clean_id(to_symbol_expr(expr).get_identifier());
  }
  else if (expr.id() == ID_index)
  {
    index_exprt indx = to_index_expr(expr);
    std::string array_string;
    if (indx.array().id() != ID_symbol)
      array_string = expr2sygus(indx.array());
    else
      array_string = id2string(to_symbol_expr(indx.array()).get_identifier());

    if (indx.index().id() != ID_infinity)
    {
      result += "select " +
                clean_id(array_string) + " ";
      if (indx.index().id() == ID_symbol || indx.index().id() == ID_constant)
        result += expr2sygus(indx.index());
      else
      {
        result += expr2sygus(indx.index());
      }
    }
    else
      return clean_id(array_string);
  }
  else if (expr.id() == ID_constant)
  {
    if (to_constant_expr(expr).type().id() == ID_unsignedbv)
    {
      result += "_ bv" + integer2string(string2integer(id2string(to_constant_expr(expr).get_value()), 16u), 10u) +
                " " + integer2string(to_unsignedbv_type(to_constant_expr(expr).type()).get_width()) + "";
    }
    else if (to_constant_expr(expr).type().id() == ID_integer)
    {
      result = clean_id(to_constant_expr(expr).get_value());
      if (result.front() == '-')
        return "(- " + result.substr(1, result.size() - 1) + ")";
      else
        return result;
    }
    else if (to_constant_expr(expr).type().id() == ID_bool)
      return result = clean_id(to_constant_expr(expr).get_value());
    else
    {
      std::cout << "Unsupported constant type" << expr.pretty() << std::endl;
    }
  }
  else if (expr.id() == ID_with)
  {
    result += "store " +
              expr2sygus(to_with_expr(expr).old()) + " " +
              expr2sygus(to_with_expr(expr).where()) + " " +
              expr2sygus(to_with_expr(expr).new_value());
  }
  else if (expr.id() == ID_forall)
  {
    result += "forall (";
    for (const auto &e : to_forall_expr(expr).variables())
      result += "(" + expr2sygus(e) + " " + type2sygus(e.type()) + ")";
    result += ") " + expr2sygus(to_forall_expr(expr).where());
  }
  else if (expr.id() == ID_exists)
  {
    result += "exists (";
    for (const auto &e : to_exists_expr(expr).variables())
      result += "(" + expr2sygus(e) + " " + type2sygus(e.type()) + ")";
    result += ") " + expr2sygus(to_exists_expr(expr).where());
  }
  else if (expr.id() == ID_let)
  {
    result += "let (";
    const auto &var = to_let_expr(expr).variables();
    const auto &val = to_let_expr(expr).values();
    for (unsigned int i = 0; i < var.size(); i++)
    {
      result += "(" + expr2sygus(var[i]) + " " + expr2sygus(val[i]) + ")";
    }

    result += ") " + expr2sygus(to_let_expr(expr).where());
  }
  else if (expr.id() == ID_typecast)
  {
    auto typecast = to_typecast_expr(expr);

    if(typecast.type().id()==ID_bool )
    {
      result += "= "+ expr2sygus(typecast.op()) + " " + expr2sygus(from_integer(1, typecast.op().type()));
    }
    else if (typecast.op().type().id()==ID_bool)
    {
      result += "ite "+ expr2sygus(typecast.op()) + " " + 
                expr2sygus(from_integer(1, typecast.type())) + "  "+ 
                expr2sygus(from_integer(0, typecast.type()));
    }
    else
    {
      return expr2sygus(to_typecast_expr(expr).op());
    }
    
  }
  else if (expr.id() == ID_extractbits)
  {
    const extractbits_exprt &extract = to_extractbits_expr(expr);
    result += "(_ extract " + expr2sygus(extract.upper()) + " " + expr2sygus(extract.lower()) + ") " + expr2sygus(extract.src());
  }
  else if (expr.id() == ID_concatenation)
  {
    const concatenation_exprt &c = to_concatenation_expr(expr);
    result += "concat " + expr2sygus(c.operands()[0]) + " " + expr2sygus(c.operands()[1]);
  }
  else if (expr.id() == ID_if)
  {
    result += "ite " + expr2sygus(to_if_expr(expr).cond()) + " " + expr2sygus(to_if_expr(expr).true_case()) + " " + expr2sygus(to_if_expr(expr).false_case());
  }
  else if (id2string(expr.id()) == "distinct")
  {
    result += "distinct";
    for (const auto &op : expr.operands())
      result += " " + expr2sygus(op);
  }
  else
  {
    // std::cout << "WARNING: unsupported expression type" << expr.pretty() << std::endl;
    result += id2string(expr.id());
    // assert(0);
  }
  result += ")"; 
  return result;
}

