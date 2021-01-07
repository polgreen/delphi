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

  std::string::size_type c_pos2 = dest.find("synth_fun::"); // 11 chars
  if (c_pos2 != std::string::npos &&
      dest.rfind("synth_fun::") == c_pos2)
    dest.erase(0, c_pos2 + 11);

  c_pos2 = dest.find("synth::"); //7 chars
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

std::string expr2sygus(const exprt &expr)
{
  return expr2sygus(expr, true);
}

std::string expr2sygus(const exprt &expr, bool use_integers)
{
  std::string result = "(";

  if (expr.id() == ID_equal)
    result += "= " + expr2sygus(expr.operands()[0], use_integers) + " " +
              expr2sygus(expr.operands()[1], use_integers);
  else if (expr.id() == ID_le)
  {
    if (to_binary_relation_expr(expr).operands()[0].id() == ID_typecast)
      result += (use_integers ? "<= " : "bvsle ") + expr2sygus(expr.operands()[0], use_integers) + " " +
                expr2sygus(expr.operands()[1], use_integers);
    else
      result += (use_integers ? "<= " : "bvule ") + expr2sygus(expr.operands()[0], use_integers) + " " +
                expr2sygus(expr.operands()[1], use_integers);
  }
  else if (expr.id() == ID_ge)
  {
    if (to_binary_relation_expr(expr).operands()[0].id() == ID_typecast)
      result += (use_integers ? ">= " : "bvsge ") + expr2sygus(expr.operands()[0], use_integers) + " " +
                expr2sygus(expr.operands()[1], use_integers);
    else
      result += (use_integers ? ">= " : "bvuge ") + expr2sygus(expr.operands()[0], use_integers) + " " +
                expr2sygus(expr.operands()[1], use_integers);
  }
  else if (expr.id() == ID_lt)
  {
    if (to_binary_relation_expr(expr).operands()[0].id() == ID_typecast)
      result += (use_integers ? "< " : "bvslt ") + expr2sygus(expr.operands()[0], use_integers) + " " +
                expr2sygus(expr.operands()[1], use_integers);
    else
      result += (use_integers ? "< " : "bvult ") + expr2sygus(expr.operands()[0], use_integers) + " " +
                expr2sygus(expr.operands()[1], use_integers);
  }
  else if (expr.id() == ID_gt)
  {
    if (to_binary_relation_expr(expr).operands()[0].id() == ID_typecast)
      result += (use_integers ? "> " : "bvsgt ") + expr2sygus(expr.operands()[0], use_integers) + " " +
                expr2sygus(expr.operands()[1], use_integers);
    else
      result += (use_integers ? "> " : "bvugt ") + expr2sygus(expr.operands()[0], use_integers) + " " +
                expr2sygus(expr.operands()[1], use_integers);
  }
  else if (expr.id() == ID_and)
  {
    result += "and";
    for (const auto &op : expr.operands())
      result += " " + expr2sygus(op, use_integers);
  }
  else if (expr.id() == ID_or)
  {
    result += "or";
    for (const auto &op : expr.operands())
      result += " " + expr2sygus(op, use_integers) ;
  }
  else if (expr.id() == ID_xor)
    result += "xor " + expr2sygus(expr.operands()[0], use_integers) + " " +
              expr2sygus(expr.operands()[1], use_integers);
  else if (expr.id() == ID_not)
    result += "not " + expr2sygus(expr.operands()[0], use_integers);

  else if (expr.id() == ID_bitand)
    result += "bvand " + expr2sygus(expr.operands()[0], use_integers) + " " +
              expr2sygus(expr.operands()[1], use_integers);
  else if (expr.id() == ID_bitor)
    result += "bvor " + expr2sygus(expr.operands()[0], use_integers) + " " +
              expr2sygus(expr.operands()[1], use_integers);
  else if (expr.id() == ID_bitxor)
    result += "bvxor " + expr2sygus(expr.operands()[0], use_integers) + " " +
              expr2sygus(expr.operands()[1], use_integers);
  else if (expr.id() == ID_bitxnor)
    result += "bvxnor " + expr2sygus(expr.operands()[0], use_integers) + " " +
              expr2sygus(expr.operands()[1], use_integers);
  else if (expr.id() == ID_bitnot)
    result += "bvnot " + expr2sygus(expr.operands()[0], use_integers);
  else if (expr.id() == ID_lshr)
    result += "bvlshr " + expr2sygus(expr.operands()[0], use_integers) + " " +
              expr2sygus(expr.operands()[1], use_integers);
  else if (expr.id() == ID_shl)
    result += "bvlshl " + expr2sygus(expr.operands()[0], use_integers) + " " +
              expr2sygus(expr.operands()[1], use_integers);
  else if (expr.id() == ID_unary_minus)
  {
    if (use_integers)
      return result = "(- " + expr2sygus(expr.operands()[0], use_integers) + ")";
    else
      result += "bvneg " + expr2sygus(expr.operands()[0], use_integers);
  }
  else if (expr.id() == ID_plus)
  {
    result += (use_integers ? "+" : "bvadd");
    for (const auto &op : expr.operands())
      result += " " + expr2sygus(op, use_integers);
  }
  else if (expr.id() == ID_minus)
    result += (use_integers ? "- "
                            : "bvsub ") +
              expr2sygus(expr.operands()[0], use_integers) + " " +
              expr2sygus(expr.operands()[1], use_integers);
  else if (expr.id() == ID_mult)
    result += (use_integers ? "* " : "bvmul ") + expr2sygus(expr.operands()[0], use_integers) + " " +
              expr2sygus(expr.operands()[1], use_integers);
  else if (expr.id() == ID_implies)
  {
    result += "=> " + expr2sygus(expr.operands()[0], use_integers) + " " + expr2sygus(expr.operands()[1], use_integers);
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
      result += " " + expr2sygus(arg, use_integers);
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
      array_string = expr2sygus(indx.array(), use_integers);
    else
      array_string = id2string(to_symbol_expr(indx.array()).get_identifier());

    if (indx.index().id() != ID_infinity)
    {
      result += "select " +
                clean_id(array_string) + " ";
      if (indx.index().id() == ID_symbol || indx.index().id() == ID_constant)
        result += expr2sygus(indx.index(), use_integers);
      else
      {
        result += expr2sygus(indx.index(), use_integers);
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
        return "(- " + result + ")";
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
              expr2sygus(to_with_expr(expr).old(), use_integers) + " " +
              expr2sygus(to_with_expr(expr).where(), use_integers) + " " +
              expr2sygus(to_with_expr(expr).new_value(), use_integers);
  }
  else if (expr.id() == ID_forall)
  {
    result += "forall (";
    for (const auto &e : to_forall_expr(expr).variables())
      result += "(" + expr2sygus(e, use_integers) + " " + type2sygus(e.type()) + ")";
    result += ") " + expr2sygus(to_forall_expr(expr).where(), use_integers);
  }
  else if (expr.id() == ID_exists)
  {
    result += "exists (";
    for (const auto &e : to_exists_expr(expr).variables())
      result += "(" + expr2sygus(e, use_integers) + " " + type2sygus(e.type()) + ")";
    result += ") " + expr2sygus(to_exists_expr(expr).where(), use_integers);
  }
  else if (expr.id() == ID_let)
  {
    result += "let (";
    const auto &var = to_let_expr(expr).variables();
    const auto &val = to_let_expr(expr).values();
    for (unsigned int i = 0; i < var.size(); i++)
    {
      result += "(" + expr2sygus(var[i], use_integers) + " " + expr2sygus(val[i], use_integers) + ")";
    }

    result += ") " + expr2sygus(to_let_expr(expr).where(), use_integers);
  }
  else if (expr.id() == ID_typecast)
  {
    // ignore typecast, they only occur when we use signed operators
    // risky behaviour..
    return expr2sygus(to_typecast_expr(expr).op(), use_integers);
  }
  else if (expr.id() == ID_extractbits)
  {
    const extractbits_exprt &extract = to_extractbits_expr(expr);
    result += "(_ extract " + expr2sygus(extract.upper(), use_integers) + " " + expr2sygus(extract.lower(), use_integers) + ") " + expr2sygus(extract.src(), use_integers);
  }
  else if (expr.id() == ID_concatenation)
  {
    const concatenation_exprt &c = to_concatenation_expr(expr);
    result += "concat " + expr2sygus(c.operands()[0], use_integers) + " " + expr2sygus(c.operands()[1], use_integers);
  }
  else if (expr.id() == ID_if)
  {
    result += "ite " + expr2sygus(to_if_expr(expr).cond(), use_integers) + " " + expr2sygus(to_if_expr(expr).true_case(), use_integers) + " " + expr2sygus(to_if_expr(expr).false_case(), use_integers);
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

std::string remove_synth_prefix(std::string in)
{
  std::string::size_type c_pos2 = in.find("synth_fun::");
  if (c_pos2 != std::string::npos &&
      in.rfind("synth_fun::") == c_pos2)
  {
    in.erase(0, c_pos2);
  }
  return in;
}

