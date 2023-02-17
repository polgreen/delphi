#include "expr2sygus.h"

#include <util/mathematical_expr.h>
#include <util/mathematical_types.h>
#include <util/arith_tools.h>
#include <util/range.h>
#include <util/expr_util.h>
#include <util/fixedbv.h>


std::size_t boolbv_width(const typet &expr_type)
{
  if (expr_type.id() == ID_signedbv)
    return to_signedbv_type(expr_type).get_width();
  else if (expr_type.id() == ID_unsignedbv)
    return to_unsignedbv_type(expr_type).get_width();
  else if (expr_type.id() == ID_bv)
    return to_bv_type(expr_type).get_width();
  else
    assert(0);
  return 0;
}

std::string convert_constant(const constant_exprt &expr)
{
  std::string result;
  const typet &expr_type=expr.type();

  if(expr_type.id()==ID_unsignedbv ||
     expr_type.id()==ID_signedbv ||
     expr_type.id()==ID_bv )
  {
    std::size_t width;
    if(expr_type.id()==ID_signedbv)
      width = to_signedbv_type(expr_type).get_width();
    else if(expr_type.id()==ID_unsignedbv)
      width = to_unsignedbv_type(expr_type).get_width();
    else
      width = to_bv_type(expr_type).get_width();

    const mp_integer value = bvrep2integer(expr.get_value(), width, false);

    result += "(_ bv" + integer2string(value)
        + " " + integer2string(width) + ")";
  }
  else if(expr_type.id()==ID_fixedbv)
  {
    const fixedbv_spect spec(to_fixedbv_type(expr_type));

    const mp_integer v = bvrep2integer(expr.get_value(), spec.width, false);

    result += "(_ bv" + integer2string(v) + " " + integer2string(spec.width) + ")";
  }
  else if(expr_type.id()==ID_floatbv)
  {
    const floatbv_typet &floatbv_type=
      to_floatbv_type(expr_type);

    // if(use_FPA_theory)
    {
      /* CBMC stores floating point literals in the most
         computationally useful form; biased exponents and
         significands including the hidden bit.  Thus some encoding
         is needed to get to IEEE-754 style representations. */

      ieee_floatt v=ieee_floatt(expr);
      size_t e=floatbv_type.get_e();
      size_t f=floatbv_type.get_f()+1;

      /* Should be sufficient, but not currently supported by mathsat */
      mp_integer binary = v.pack();

      result += "((_ to_fp " + integer2string(e) + " " + integer2string(f) + ")"
          + " #b" + integer2binary(v.pack(), v.spec.width()) + ")";
    }
  }
  else if(expr_type.id()==ID_bool)
  {
    if(expr.is_true())
      result += "true";
    else if(expr.is_false())
      result += "false";
    else
      UNEXPECTEDCASE("unknown Boolean constant");
  }
  else if(expr_type.id()==ID_rational)
  {
    std::string value=id2string(expr.get_value());
    size_t pos=value.find("/");

    if(pos==std::string::npos)
      result += value + ".0";
    else
    {
      result += "(/ " + value.substr(0, pos) + ".0 "
                   + value.substr(pos+1) + ".0)";
    }
  }
  else if(expr_type.id()==ID_integer || expr_type.id()==ID_real)
  {
    std::string value = id2string(expr.get_value());
    auto pos = value.find('-');
    if(pos!=std::string::npos)
    {
      std::string number_str;
      number_str.reserve(value.size());
      for (auto ch : value)
        if (ch != '-')
          number_str += ch;
      return"(- "+ number_str +")";
    }
    return id2string(expr.get_value());
  }
  else
    UNEXPECTEDCASE("unknown constant: "+expr_type.id_string());
  return result;
}


std::string convert_expr(const exprt &expr)
{
  std::string result; 
  // huge monster case split over expression id
  if(expr.id()==ID_symbol)
  {
    const irep_idt &id = to_symbol_expr(expr).get_identifier();
    DATA_INVARIANT(!id.empty(), "symbol must have identifier");
    result = clean_id(id);
  }
  else if(expr.id()==ID_nondet_symbol)
  {
    const irep_idt &id = to_nondet_symbol_expr(expr).get_identifier();
    DATA_INVARIANT(!id.empty(), "nondet symbol must have identifier");
    result = clean_id(id);
  }
  else if(expr.id()==ID_typecast)
  {
    return convert_typecast(to_typecast_expr(expr));
  }
  else if(expr.id()==ID_floatbv_typecast)
  {
    return convert_floatbv_typecast(to_floatbv_typecast_expr(expr));
  }
  else if(expr.id()==ID_constant)
  {
    return convert_constant(to_constant_expr(expr));
  }
  else if(expr.id() == ID_concatenation && expr.operands().size() == 1)
  {
    DATA_INVARIANT_WITH_DIAGNOSTICS(
      expr.type() == expr.operands().front().type(),
      "concatenation over a single operand should have matching types",
      expr.pretty());

    return convert_expr(expr.operands().front());
  }
  else if(expr.id()==ID_concatenation ||
          expr.id()==ID_bitand ||
          expr.id()==ID_bitor ||
          expr.id()==ID_bitxor ||
          expr.id()==ID_bitnand ||
          expr.id()==ID_bitnor)
  {
    DATA_INVARIANT_WITH_DIAGNOSTICS(
      expr.operands().size() >= 2,
      "given expression should have at least two operands",
      expr.id_string());

    result+= "(";

    if(expr.id()==ID_concatenation)
      result+= "concat";
    else if(expr.id()==ID_bitand)
      result+= "bvand";
    else if(expr.id()==ID_bitor)
      result+= "bvor";
    else if(expr.id()==ID_bitxor)
      result+= "bvxor";
    else if(expr.id()==ID_bitnand)
      result+= "bvnand";
    else if(expr.id()==ID_bitnor)
      result+= "bvnor";

    forall_operands(it, expr)
    {
      result+= " ";
      result += flatten2bv(*it);
    }

    result+=  ")";
  }
  else if(expr.id()==ID_bitnot)
  {
    const bitnot_exprt &bitnot_expr = to_bitnot_expr(expr);

    if(bitnot_expr.type().id() == ID_vector)
    {
      // if(use_datatypes)
      // {
      //   const std::string &smt_typename = datatype_map.at(bitnot_expr.type());

      //   // extract elements
      //   const vector_typet &vector_type = to_vector_type(bitnot_expr.type());

      //   mp_integer size = numeric_cast_v<mp_integer>(vector_type.size());

      //   result+= "(let ((?vectorop ";
      //   result += convert_expr(bitnot_expr.op());
      //   result+= ")) ";

      //   result+= "(mk-" + smt_typename;

      //   typet index_type=vector_type.size().type();

      //   // do bitnot component-by-component
      //   for(mp_integer i=0; i!=size; ++i)
      //   {
      //     result+= " (bvnot (" + smt_typename + "." + (size-i-1)
      //         + " ?vectorop))";
      //   }

      //   result+= "))"; // mk-, let
      // }
      // else
      //   SMT2_TODO("bitnot for vectors");
    }
    else
    {
      result+= "(bvnot ";
      result += convert_expr(bitnot_expr.op());
      result+= ")";
    }
  }
  else if(expr.id()==ID_unary_minus)
  {
    const unary_minus_exprt &unary_minus_expr = to_unary_minus_expr(expr);

    if(
      unary_minus_expr.type().id() == ID_rational ||
      unary_minus_expr.type().id() == ID_integer ||
      unary_minus_expr.type().id() == ID_real)
    {
      result+= "(- ";
      result += convert_expr(unary_minus_expr.op());
      result+= ")";
    }
    else if(unary_minus_expr.type().id() == ID_floatbv)
    {
      // this has no rounding mode
      // if(use_FPA_theory)
      {
        result+= "(fp.neg ";
        result += convert_expr(unary_minus_expr.op());
        result+= ")";
      }
    }
    else if(unary_minus_expr.type().id() == ID_vector)
    {
      SMT2_TODO("unary minus for vector");
    }
    else
    {
      result+= "(bvneg ";
      result += convert_expr(unary_minus_expr.op());
      result+= ")";
    }
  }
  else if(expr.id()==ID_unary_plus)
  {
    // A no-op (apart from type promotion)
    result += convert_expr(to_unary_plus_expr(expr).op());
  }
  else if(expr.id()==ID_sign)
  {
    const sign_exprt &sign_expr = to_sign_expr(expr);

    const typet &op_type = sign_expr.op().type();

    if(op_type.id()==ID_floatbv)
    {
      // if(use_FPA_theory)
      {
        result+= "(fp.isNegative ";
        result += convert_expr(sign_expr.op());
        result+= ")";
      }
    }
    else if(op_type.id()==ID_signedbv)
    {
      std::size_t op_width=to_signedbv_type(op_type).get_width();

      result+= "(bvslt ";
      result += convert_expr(sign_expr.op());
      result+= " (_ bv0 " + integer2string(op_width) + "))";
    }
    else
      INVARIANT_WITH_DIAGNOSTICS(
        false,
        "sign should not be applied to unsupported type",
        sign_expr.type().id_string());
  }
  else if(expr.id()==ID_if)
  {
    const if_exprt &if_expr = to_if_expr(expr);

    result+= "(ite ";
    result += convert_expr(if_expr.cond());
    result+= " ";
    result += convert_expr(if_expr.true_case());
    result+= " ";
    result += convert_expr(if_expr.false_case());
    result+= ")";
  }
  else if(expr.id()==ID_and ||
          expr.id()==ID_or ||
          expr.id()==ID_xor)
  {
    DATA_INVARIANT(
      expr.type().id() == ID_bool,
      "logical and, or, and xor expressions should have Boolean type");
    DATA_INVARIANT(
      expr.operands().size() >= 2,
      "logical and, or, and xor expressions should have at least two operands");

    result+= "(" + id2string(expr.id());
    forall_operands(it, expr)
    {
      result+= " ";
      result += convert_expr(*it);
    }
    result+= ")";
  }
  else if(expr.id()==ID_implies)
  {
    const implies_exprt &implies_expr = to_implies_expr(expr);

    DATA_INVARIANT(
      implies_expr.type().id() == ID_bool,
      "implies expression should have Boolean type");

    result+= "(=> ";
    result += convert_expr(implies_expr.op0());
    result+= " ";
    result += convert_expr(implies_expr.op1());
    result+= ")";
  }
  else if(expr.id()==ID_not)
  {
    const not_exprt &not_expr = to_not_expr(expr);

    DATA_INVARIANT(
      not_expr.type().id() == ID_bool,
      "not expression should have Boolean type");

    result+= "(not ";
    result += convert_expr(not_expr.op());
    result+= ")";
  }
  else if(expr.id() == ID_equal)
  {
    const equal_exprt &equal_expr = to_equal_expr(expr);

    DATA_INVARIANT(
      equal_expr.op0().type() == equal_expr.op1().type(),
      "operands of equal expression shall have same type");

    result+= "(= ";
    result += convert_expr(equal_expr.op0());
    result+= " ";
    result += convert_expr(equal_expr.op1());
    result+= ")";
  }
  else if(expr.id() == ID_notequal)
  {
    const notequal_exprt &notequal_expr = to_notequal_expr(expr);

    DATA_INVARIANT(
      notequal_expr.op0().type() == notequal_expr.op1().type(),
      "operands of not equal expression shall have same type");

    result+= "(not (= ";
    result += convert_expr(notequal_expr.op0());
    result+= " ";
    result += convert_expr(notequal_expr.op1());
    result+= "))";
  }
  else if(expr.id()==ID_ieee_float_equal ||
          expr.id()==ID_ieee_float_notequal)
  {
    // These are not the same as (= A B)
    // because of NaN and negative zero.
    const auto &rel_expr = to_binary_relation_expr(expr);

    DATA_INVARIANT(
      rel_expr.lhs().type() == rel_expr.rhs().type(),
      "operands of float equal and not equal expressions shall have same type");

    // The FPA theory properly treats NaN and negative zero.
    {
      if(rel_expr.id() == ID_ieee_float_notequal)
        result+= "(not ";

      result+= "(fp.eq ";
      result += convert_expr(rel_expr.lhs());
      result+= " ";
      result += convert_expr(rel_expr.rhs());
      result+= ")";

      if(rel_expr.id() == ID_ieee_float_notequal)
        result+= ")";
    }
  }
  else if(expr.id()==ID_le ||
          expr.id()==ID_lt ||
          expr.id()==ID_ge ||
          expr.id()==ID_gt)
  {
    result += convert_relation(to_binary_relation_expr(expr));
  }
  else if(expr.id()==ID_plus)
  {
    result += convert_plus(to_plus_expr(expr));
  }
  else if(expr.id()==ID_floatbv_plus)
  {
    result += convert_floatbv_plus(to_ieee_float_op_expr(expr));
  }
  else if(expr.id()==ID_minus)
  {
    result += convert_minus(to_minus_expr(expr));
  }
  else if(expr.id()==ID_floatbv_minus)
  {
    result += convert_floatbv_minus(to_ieee_float_op_expr(expr));
  }
  else if(expr.id()==ID_div)
  {
    result += convert_div(to_div_expr(expr));
  }
  else if(expr.id()==ID_floatbv_div)
  {
    result += convert_floatbv_div(to_ieee_float_op_expr(expr));
  }
  else if(expr.id()==ID_mod)
  {
    result += convert_mod(to_mod_expr(expr));
  }
  else if(expr.id()==ID_mult)
  {
    result += convert_mult(to_mult_expr(expr));
  }
  else if(expr.id()==ID_floatbv_mult)
  {
    result += convert_floatbv_mult(to_ieee_float_op_expr(expr));
  }
  else if(expr.id()==ID_index)
  {
    result += convert_index(to_index_expr(expr));
  }
  else if(expr.id()==ID_ashr ||
          expr.id()==ID_lshr ||
          expr.id()==ID_shl)
  {
    const shift_exprt &shift_expr = to_shift_expr(expr);
    const typet &type = shift_expr.type();

    if(type.id()==ID_unsignedbv ||
       type.id()==ID_signedbv ||
       type.id()==ID_bv)
    {
      if(shift_expr.id() == ID_ashr)
        result+= "(bvashr ";
      else if(shift_expr.id() == ID_lshr)
        result+= "(bvlshr ";
      else if(shift_expr.id() == ID_shl)
        result+= "(bvshl ";
      else
        UNREACHABLE;

      result += convert_expr(shift_expr.op());
      result+= " ";

      // SMT2 requires the shift distance to have the same width as
      // the value that is shifted -- odd!

      // if(shift_expr.distance().type().id() == ID_integer)
      // {
      //   const mp_integer i =
      //     numeric_cast_v<mp_integer>(to_constant_expr(shift_expr.distance()));

      //   // shift distance must be bit vector
      //   std::size_t width_op0 = boolbv_width(shift_expr.op().type());
      //   exprt tmp=from_integer(i, unsignedbv_typet(width_op0));
      //   result += convert_expr(tmp);
      // }
      if(
        shift_expr.distance().type().id() == ID_signedbv ||
        shift_expr.distance().type().id() == ID_unsignedbv)
      {
        std::size_t width_op0 = boolbv_width(shift_expr.op().type());
        std::size_t width_op1 = boolbv_width(shift_expr.distance().type());

        if(width_op0==width_op1)
          result += convert_expr(shift_expr.distance());
        else if(width_op0>width_op1)
        {
          result+= "((_ zero_extend " + integer2string(width_op0-width_op1) + ") ";
          result += convert_expr(shift_expr.distance());
          result+= ")"; // zero_extend
        }
        else // width_op0<width_op1
        {
          result+= "((_ extract " + integer2string(width_op0-1) + " 0) ";
          result += convert_expr(shift_expr.distance());
          result+= ")"; // extract
        }
      }
      else
        UNEXPECTEDCASE(
          "unsupported distance type for " + shift_expr.id_string() + ": " +
          type.id_string());

      result+= ")"; // bv*sh
    }
    else
      UNEXPECTEDCASE(
        "unsupported type for " + shift_expr.id_string() + ": " +
        type.id_string());
  }
  else if(expr.id() == ID_rol || expr.id() == ID_ror)
  {
    const shift_exprt &shift_expr = to_shift_expr(expr);
    const typet &type = shift_expr.type();

    if(
      type.id() == ID_unsignedbv || type.id() == ID_signedbv ||
      type.id() == ID_bv)
    {
      // SMT-LIB offers rotate_left and rotate_right, but these require a
      // constant distance.
      if(shift_expr.id() == ID_rol)
        result+= "((_ rotate_left";
      else if(shift_expr.id() == ID_ror)
        result+= "((_ rotate_right";
      else
        UNREACHABLE;

      result+= ' ';

      auto distance_int_op = numeric_cast<mp_integer>(shift_expr.distance());

      if(distance_int_op.has_value())
      {
        result+= integer2string(distance_int_op.value());
      }
      else
        UNEXPECTEDCASE(
          "distance type for " + shift_expr.id_string() + "must be constant");

      result+= ") ";
      result += convert_expr(shift_expr.op());

      result+= ")"; // rotate_*
    }
    else
      UNEXPECTEDCASE(
        "unsupported type for " + shift_expr.id_string() + ": " +
        type.id_string());
  }
  else if(expr.id()==ID_with)
  {
    result += convert_with(to_with_expr(expr));
  }
  // else if(expr.id()==ID_member)
  // {
  //   result += convert_member(to_member_expr(expr));
  // }
  // else if(expr.id()==ID_pointer_offset)
  // {
  //   const auto &op = to_unary_expr(expr).op();

  //   DATA_INVARIANT(
  //     op.type().id() == ID_pointer,
  //     "operand of pointer offset expression shall be of pointer type");

  //   std::size_t offset_bits =
  //     boolbv_width(op.type()) - config.bv_encoding.object_bits;
  //   std::size_t result_width=boolbv_width(expr.type());

  //   // max extract width
  //   if(offset_bits>result_width)
  //     offset_bits=result_width;

  //   // too few bits?
  //   if(result_width>offset_bits)
  //     result+= "((_ zero_extend " + result_width-offset_bits + ") ";

  //   result+= "((_ extract " + offset_bits-1 + " 0) ";
  //   result += convert_expr(op);
  //   result+= ")";

  //   if(result_width>offset_bits)
  //     result+= ")"; // zero_extend
  // }
  else if(expr.id()==ID_extractbit)
  {
    const extractbit_exprt &extractbit_expr = to_extractbit_expr(expr);

    if(extractbit_expr.index().is_constant())
    {
      const mp_integer i =
        numeric_cast_v<mp_integer>(to_constant_expr(extractbit_expr.index()));

      result+= "(= ((_ extract " + integer2string(i) + " " + integer2string(i) + ") ";
      flatten2bv(extractbit_expr.src());
      result+= ") #b1)";
    }
    else
    {
      result+= "(= ((_ extract 0 0) ";
      // the arguments of the shift need to have the same width
      result+= "(bvlshr ";
      flatten2bv(extractbit_expr.src());
      typecast_exprt tmp(extractbit_expr.index(), extractbit_expr.src().type());
      result += convert_expr(tmp);
      result+= ")) bin1)"; // bvlshr, extract, =
    }
  }
  else if(expr.id()==ID_extractbits)
  {
    const extractbits_exprt &extractbits_expr = to_extractbits_expr(expr);

    if(
      extractbits_expr.upper().is_constant() &&
      extractbits_expr.lower().is_constant())
    {
      mp_integer op1_i =
        numeric_cast_v<mp_integer>(to_constant_expr(extractbits_expr.upper()));
      mp_integer op2_i =
        numeric_cast_v<mp_integer>(to_constant_expr(extractbits_expr.lower()));

      if(op2_i>op1_i)
        std::swap(op1_i, op2_i);

      // now op1_i>=op2_i

      result+= "((_ extract " + integer2string(op1_i) + " " + integer2string(op2_i) + ") ";
      flatten2bv(extractbits_expr.src());
      result+= ")";
    }
    else
    {
      #if 0
      result+= "(= ((_ extract 0 0) ";
      // the arguments of the shift need to have the same width
      result+= "(bvlshr ";
      result += convert_expr(expr.op0());
      typecast_exprt tmp(expr.op0().type());
      tmp.op0()=expr.op1();
      result += convert_expr(tmp);
      result+= ")) bin1)"; // bvlshr, extract, =
      #endif
      SMT2_TODO("smt2: extractbits with non-constant index");
    }
  }
  else if(expr.id()==ID_byte_extract_little_endian ||
          expr.id()==ID_byte_extract_big_endian)
  {
    INVARIANT(
      false, "byte_extract ops should be lowered in prepare_for_convert_expr");
  }
  else if(expr.id()==ID_byte_update_little_endian ||
          expr.id()==ID_byte_update_big_endian)
  {
    INVARIANT(
      false, "byte_update ops should be lowered in prepare_for_convert_expr");
  }
  // else if(expr.id()==ID_width)
  // {
  //   // std::size_t result_width=boolbv_width(expr.type());
  //   // CHECK_RETURN(result_width != 0);

  //   // std::size_t op_width = boolbv_width(to_unary_expr(expr).op().type());
  //   // CHECK_RETURN(op_width != 0);

  //   result+= "(_ bv" + integer2string(op_width/8)
  //       + " " + integer2string(result_width) + ")";
  // }
  else if(expr.id()==ID_abs)
  {
    const abs_exprt &abs_expr = to_abs_expr(expr);

    const typet &type = abs_expr.type();

    if(type.id()==ID_signedbv)
    {
      std::size_t result_width = to_signedbv_type(type).get_width();

      result+= "(ite (bvslt ";
      result += convert_expr(abs_expr.op());
      result+= " (_ bv0 " + integer2string(result_width) + ")) ";
      result+= "(bvneg ";
      result += convert_expr(abs_expr.op());
      result+= ") ";
      result += convert_expr(abs_expr.op());
      result+= ")";
    }
    else if(type.id()==ID_fixedbv)
    {
      std::size_t result_width=to_fixedbv_type(type).get_width();

      result+= "(ite (bvslt ";
      result += convert_expr(abs_expr.op());
      result+= " (_ bv0 " + integer2string(result_width) + ")) ";
      result+= "(bvneg ";
      result += convert_expr(abs_expr.op());
      result+= ") ";
      result += convert_expr(abs_expr.op());
      result+= ")";
    }
    else if(type.id()==ID_floatbv)
    {
      result+= "(fp.abs ";
      result += convert_expr(abs_expr.op());
      result+= ")";
  
    }
    else
      UNREACHABLE;
  }
  else if(expr.id()==ID_isnan)
  {
    const isnan_exprt &isnan_expr = to_isnan_expr(expr);

    const typet &op_type = isnan_expr.op().type();

    if(op_type.id()==ID_fixedbv)
      result+= "false";
    else if(op_type.id()==ID_floatbv)
    {
        result+= "(fp.isNaN ";
        result += convert_expr(isnan_expr.op());
        result+= ")";
    }
    else
      UNREACHABLE;
  }
  else if(expr.id()==ID_isfinite)
  {
    const isfinite_exprt &isfinite_expr = to_isfinite_expr(expr);

    const typet &op_type = isfinite_expr.op().type();

    if(op_type.id()==ID_fixedbv)
      result+= "true";
    else if(op_type.id()==ID_floatbv)
    {

        result+= "(and ";

        result+= "(not (fp.isNaN ";
        result += convert_expr(isfinite_expr.op());
        result+= "))";

        result+= "(not (fp.isInf ";
        result += convert_expr(isfinite_expr.op());
        result+= "))";

        result+= ")";
    }
    else
      UNREACHABLE;
  }
  else if(expr.id()==ID_isinf)
  {
    const isinf_exprt &isinf_expr = to_isinf_expr(expr);

    const typet &op_type = isinf_expr.op().type();

    if(op_type.id()==ID_fixedbv)
      result+= "false";
    else if(op_type.id()==ID_floatbv)
    {
      {
        result+= "(fp.isInfinite ";
        result += convert_expr(isinf_expr.op());
        result+= ")";
      }
    }
    else
      UNREACHABLE;
  }
  else if(expr.id()==ID_isnormal)
  {
    const isnormal_exprt &isnormal_expr = to_isnormal_expr(expr);

    const typet &op_type = isnormal_expr.op().type();

    if(op_type.id()==ID_fixedbv)
      result+= "true";
    else if(op_type.id()==ID_floatbv)
    {
      {
        result+= "(fp.isNormal ";
        result += convert_expr(isnormal_expr.op());
        result+= ")";
      }
    }
    else
      UNREACHABLE;
  }
  // else if(expr.id()==ID_overflow_plus ||
  //         expr.id()==ID_overflow_minus)
  // {
  //   const auto &op0 = to_binary_expr(expr).op0();
  //   const auto &op1 = to_binary_expr(expr).op1();

  //   DATA_INVARIANT(
  //     expr.type().id() == ID_bool,
  //     "overflow plus and overflow minus expressions shall be of Boolean type");

  //   bool subtract=expr.id()==ID_overflow_minus;
  //   const typet &op_type = op0.type();
  //   std::size_t width=boolbv_width(op_type);

  //   if(op_type.id()==ID_signedbv)
  //   {
  //     // an overflow occurs if the top two bits of the extended sum differ
  //     result+= "(let ((?sum (";
  //     result+= (subtract?"bvsub":"bvadd");
  //     result+= " ((_ sign_extend 1) ";
  //     result += convert_expr(op0);
  //     result+= ")";
  //     result+= " ((_ sign_extend 1) ";
  //     result += convert_expr(op1);
  //     result+= ")))) "; // sign_extend, bvadd/sub let2
  //     result+= "(not (= "
  //                  "((_ extract " + width + " " + width + ") ?sum) "
  //                  "((_ extract " + (width-1) + " " + (width-1) + ") ?sum)";
  //     result+= ")))"; // =, not, let
  //   }
  //   else if(op_type.id()==ID_unsignedbv ||
  //           op_type.id()==ID_pointer)
  //   {
  //     // overflow is simply carry-out
  //     result+= "(= ";
  //     result+= "((_ extract " + width + " " + width + ") ";
  //     result+= "(" + (subtract?"bvsub":"bvadd");
  //     result+= " ((_ zero_extend 1) ";
  //     result += convert_expr(op0);
  //     result+= ")";
  //     result+= " ((_ zero_extend 1) ";
  //     result += convert_expr(op1);
  //     result+= ")))"; // zero_extend, bvsub/bvadd, extract
  //     result+= " #b1)"; // =
  //   }
  //   else
  //     INVARIANT_WITH_DIAGNOSTICS(
  //       false,
  //       "overflow check should not be performed on unsupported type",
  //       op_type.id_string());
  // }
  // else if(expr.id()==ID_overflow_mult)
  // {
  //   const auto &op0 = to_binary_expr(expr).op0();
  //   const auto &op1 = to_binary_expr(expr).op1();

  //   DATA_INVARIANT(
  //     expr.type().id() == ID_bool,
  //     "overflow mult expression shall be of Boolean type");

  //   // No better idea than to multiply with double the bits and then compare
  //   // with max value.

  //   const typet &op_type = op0.type();
  //   std::size_t width=boolbv_width(op_type);

  //   if(op_type.id()==ID_signedbv)
  //   {
  //     result+= "(let ( (prod (bvmul ((_ sign_extend " + width + ") ";
  //     result += convert_expr(op0);
  //     result+= ") ((_ sign_extend " + width + ") ";
  //     result += convert_expr(op1);
  //     result+= ")) )) ";
  //     result+= "(or (bvsge prod (_ bv" + power(2, width-1) + " "
  //         + width*2 + "))";
  //     result+= " (bvslt prod (bvneg (_ bv" + power(2, width-1) + " "
  //         + width*2 + ")))))";
  //   }
  //   else if(op_type.id()==ID_unsignedbv)
  //   {
  //     result+= "(bvuge (bvmul ((_ zero_extend " + width + ") ";
  //     result += convert_expr(op0);
  //     result+= ") ((_ zero_extend " + width + ") ";
  //     result += convert_expr(op1);
  //     result+= ")) (_ bv" + power(2, width) + " " + width*2 + "))";
  //   }
  //   else
  //     INVARIANT_WITH_DIAGNOSTICS(
  //       false,
  //       "overflow check should not be performed on unsupported type",
  //       op_type.id_string());
  // }
  // else if(expr.id()==ID_array)
  // {
  //   result+= it->second;
  // }
  else if(expr.id()==ID_forall ||
          expr.id()==ID_exists)
  {
    const quantifier_exprt &quantifier_expr = to_quantifier_expr(expr);

    if(quantifier_expr.id() == ID_forall)
      result+= "(forall ";
    else if(quantifier_expr.id() == ID_exists)
      result+= "(exists ";

    result+= "(";
    for(const auto &v: quantifier_expr.variables())
    {
      result+= "(";
      result += convert_expr(v);
      result+= " ";
      result += convert_type(v.type());
      result+= ") ";
    }
    result+= ")";

    result += convert_expr(quantifier_expr.where());

    result+= ")";
  }
  else if(expr.id()==ID_vector)
  {
    const vector_exprt &vector_expr = to_vector_expr(expr);
    const vector_typet &vector_type = to_vector_type(vector_expr.type());

    mp_integer size = numeric_cast_v<mp_integer>(vector_type.size());

    DATA_INVARIANT(
      size == vector_expr.operands().size(),
      "size indicated by type shall be equal to the number of operands");

    result+= "(concat";

    // build component-by-component
    forall_operands(it, vector_expr)
    {
      result+= " ";
      result += convert_expr(*it);
    }

    result+= ")"; // mk-... or concat
  }
  else if(expr.id()==ID_let)
  {
    const let_exprt &let_expr=to_let_expr(expr);
    const auto &variables = let_expr.variables();
    const auto &values = let_expr.values();

    result+= "(let (";
    bool first = true;

    for(auto &binding : make_range(variables).zip(values))
    {
      if(first)
        first = false;
      else
        result+= ' ';

      result+= '(';
      result += convert_expr(binding.first);
      result+= ' ';
      result += convert_expr(binding.second);
      result+= ')';
    }

    result+= ") "; // bindings

    result += convert_expr(let_expr.where());
    result+= ')'; // let
  }
  else if(expr.id()==ID_constraint_select_one)
  {
    UNEXPECTEDCASE(
      "smt2_convt::convert_expr: '" + expr.id_string() +
      "' is not yet supported");
  }
  else if(expr.id() == ID_bswap)
  {
    const bswap_exprt &bswap_expr = to_bswap_expr(expr);

    DATA_INVARIANT(
      bswap_expr.op().type() == bswap_expr.type(),
      "operand of byte swap expression shall have same type as the expression");

    // first 'let' the operand
    result+= "(let ((bswap_op ";
    result += convert_expr(bswap_expr.op());
    result+= ")) ";

    if(
      bswap_expr.type().id() == ID_signedbv ||
      bswap_expr.type().id() == ID_unsignedbv)
    {
      const std::size_t width =
        to_bitvector_type(bswap_expr.type()).get_width();

      const std::size_t bits_per_byte = bswap_expr.get_bits_per_byte();

      // width must be multiple of bytes
      DATA_INVARIANT(
        width % bits_per_byte == 0,
        "bit width indicated by type of bswap expression should be a multiple "
        "of the number of bits per byte");

      const std::size_t bytes = width / bits_per_byte;

      if(bytes <= 1)
        result+= "bswap_op";
      else
      {
        // do a parallel 'let' for each byte
        result+= "(let (";

        for(std::size_t byte = 0; byte < bytes; byte++)
        {
          if(byte != 0)
            result+= ' ';
          result+= "(bswap_byte_" + integer2string(byte) + ' ';
          result+= "((_ extract " + integer2string(byte * bits_per_byte + (bits_per_byte - 1))
              + " " + integer2string(byte * bits_per_byte) + ") bswap_op)";
          result+= ')';
        }

        result+= ") ";

        // now stitch back together with 'concat'
        result+= "(concat";

        for(std::size_t byte = 0; byte < bytes; byte++)
          result+= " bswap_byte_" + integer2string(byte);

        result+= ')'; // concat
        result+= ')'; // let bswap_byte_*
      }
    }
    else
      UNEXPECTEDCASE("bswap must get bitvector operand");

    result+= ')'; // let bswap_op
  }
  else if (expr.id()==ID_function_application)
  {
    auto func_app = to_function_application_expr(expr);

// if 0 args, no parenthesis
    if(func_app.arguments().size()==0)
      return id2string(to_symbol_expr(func_app.function()).get_identifier());

    result+= '('+ id2string(to_symbol_expr(func_app.function()).get_identifier()) + " ";
    for(const auto &arg: func_app.arguments())
    {
      result += convert_expr(arg);
      result+=" ";
    }  
    result+=')';  
  }
  else if (expr.id()==ID_tuple)
  {
    for(const auto &op: expr.operands())
      result += convert_expr(op);
  }
  else
  {
    std::cout<<"Got id" << expr.id() <<std::endl;
    INVARIANT_WITH_DIAGNOSTICS(
      false,
      "smt2_convt::convert_expr should not be applied to unsupported type",
      expr.pretty());
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
  std::string result ="(declare-var ";
  result += clean_id(symbol.get_identifier()) +" " + type2sygus(symbol.type()) + ")\n";
  return result;
}


std::string expr2sygus_fun_def(const symbol_exprt &function, const exprt&body)
{
  std::vector<irep_idt>params;
  const auto &func_type = to_mathematical_function_type(function.type());
  for(std::size_t i=0; i<func_type.domain().size(); i++)
    params.push_back("parameter"+integer2string(i));

  return expr2sygus_fun_def(function, body, params);
}

std::string expr2sygus_fun_def(const symbol_exprt &function, const exprt&body, std::vector<irep_idt> parameters)
{
  INVARIANT(function.type().id()==ID_mathematical_function, "unsupported function definition type");
  std::string result = "(define-fun " + clean_id(function.get_identifier()) + " (";
  const auto &func_type = to_mathematical_function_type(function.type());

  for(std::size_t i=0; i<func_type.domain().size(); i++)
  {
    result+="( "+ clean_id(parameters[i]) +" "+type2sygus(func_type.domain()[i]) + ")"; 
  }
  result +=")\n " + type2sygus(func_type.codomain()) + " " + expr2sygus(body) + ")\n";
  return result;
}

std::string expr2sygus_fun_dec(const symbol_exprt &function)
{
  // INVARIANT(function.type().id()==ID_mathematical_function, "unsupported function definition type");
  std::string result = "(declare-fun " + clean_id(function.get_identifier()) + " (";
  if(function.type().id()==ID_mathematical_function)
  {
    const auto &func_type = to_mathematical_function_type(function.type());

    for (std::size_t i = 0; i < func_type.domain().size(); i++)
      result += type2sygus(func_type.domain()[i]) + " ";

    result += ")\n " + type2sygus(func_type.codomain()) + ")\n";
  }
  else
  {
    result += ") " + type2sygus(function.type()) + ")\n";
  }
  return result;
}

std::string synth_fun_dec(const irep_idt &id, const synth_functiont &definition)
{
  std::string result = "(synth-fun " + clean_id(id);

  if(definition.type.id()!=ID_mathematical_function)
  {
    result += "()" + type2sygus(definition.type);
  }
  else
  {
    result += "(";
    const auto &func_type = to_mathematical_function_type(definition.type);
    for (std::size_t i = 0; i < definition.parameters.size(); i++)
    {
      result += "(" + clean_id(definition.parameters[i]) + " " + type2sygus(func_type.domain()[i]) + ")";
    }
    result += ")\n " + type2sygus(func_type.codomain()) + "\n";
  }
  // grammar is empty
  if(definition.grammar.nt_ids.size()==0)
    return result += ")\n";

  std::string nts = "(";
  std::string rules = "(";
  // declare nonterminals
  for(std::size_t i=0; i< definition.grammar.nt_ids.size(); i++)
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


std::string synth_fun_dec(const irep_idt &id, const synth_functiont &definition, const std::string &override_grammar)
{
  std::string result = "(synth-fun " + clean_id(id);

  if(definition.type.id()!=ID_mathematical_function)
  {
    result += "()" + type2sygus(definition.type);
  }
  else
  {
    result += "(";
    const auto &func_type = to_mathematical_function_type(definition.type);
    for (std::size_t i = 0; i < definition.parameters.size(); i++)
    {
      result += "(" + clean_id(definition.parameters[i]) + " " + type2sygus(func_type.domain()[i]) + ")";
    }
    result += ")\n " + type2sygus(func_type.codomain()) + "\n";
  }
  // override grammar
  return result + override_grammar + "\n)\n";
}



std::string expr2sygus(const exprt &expr)
{
  return convert_expr(expr);
}

std::string type2sygus(const typet &type)
{
  return convert_type(type);
}

std::string convert_relation(const binary_relation_exprt &expr)
{
  std::string result;
  const typet &op_type=expr.op0().type();

  if(op_type.id()==ID_unsignedbv ||
     op_type.id()==ID_pointer ||
     op_type.id()==ID_bv)
  {
    result +="(";
    if(expr.id()==ID_le)
      result +="bvule";
    else if(expr.id()==ID_lt)
      result +="bvult";
    else if(expr.id()==ID_ge)
      result +="bvuge";
    else if(expr.id()==ID_gt)
      result +="bvugt";

    result +=" ";
    result += convert_expr(expr.op0());
    result +=" ";
    result += convert_expr(expr.op1());
    result +=")";
  }
  else if(op_type.id()==ID_signedbv ||
          op_type.id()==ID_fixedbv)
  {
    result +="(";
    if(expr.id()==ID_le)
      result +="bvsle";
    else if(expr.id()==ID_lt)
      result +="bvslt";
    else if(expr.id()==ID_ge)
      result +="bvsge";
    else if(expr.id()==ID_gt)
      result +="bvsgt";

    result +=" ";
    result += convert_expr(expr.op0());
    result +=" ";
    result += convert_expr(expr.op1());
    result +=")";
  }
  else if(op_type.id()==ID_floatbv)
  {
    // if(use_FPA_theory)
    {
      result +="(";
      if(expr.id()==ID_le)
        result +="fp.leq";
      else if(expr.id()==ID_lt)
        result +="fp.lt";
      else if(expr.id()==ID_ge)
        result +="fp.geq";
      else if(expr.id()==ID_gt)
        result +="fp.gt";

      result +=" ";
      result += convert_expr(expr.op0());
      result +=" ";
      result += convert_expr(expr.op1());
      result +=")";
    }
    // else
    //   result += convert_floatbv(expr);
  }
  else if(op_type.id()==ID_rational ||
          op_type.id()==ID_integer)
  {
    result +="(";
    if(expr.id()==ID_le)
      result +="<=";
    else if(expr.id()==ID_lt)
      result +="<";
    else if(expr.id()==ID_ge)
      result +=">=";
    else if(expr.id()==ID_gt)
      result +=">";

    result +=" ";
    result += convert_expr(expr.op0());
    result +=" ";
    result += convert_expr(expr.op1());
    result +=")";
  }
  else
    UNEXPECTEDCASE(
      "unsupported type for "+expr.id_string()+": "+op_type.id_string());
  return result;
}

std::string convert_plus(const plus_exprt &expr)
{
  std::string result;
  if(
    expr.type().id() == ID_rational || expr.type().id() == ID_integer ||
    expr.type().id() == ID_real)
  {
    // these are multi-ary in SMT-LIB2
    result +="(+";

    for(const auto &op : expr.operands())
    {
      result +=' ';
      result += convert_expr(op);
    }

    result +=')';
  }
  else if(
    expr.type().id() == ID_unsignedbv || expr.type().id() == ID_signedbv ||
    expr.type().id() == ID_fixedbv)
  {
    // These could be chained, i.e., need not be binary,
    // but at least MathSat doesn't like that.
    if(expr.operands().size() == 2)
    {
      result +="(bvadd ";
      result += convert_expr(expr.op0());
      result +=" ";
      result += convert_expr(expr.op1());
      result +=")";
    }
    else
    {
      result += convert_plus(to_plus_expr(make_binary(expr)));
    }
  }
  else if(expr.type().id() == ID_floatbv)
  {
    // Floating-point additions should have be been converted
    // to ID_floatbv_plus during symbolic execution, adding
    // the rounding mode.  See smt2_convt::convert_floatbv_plus.
    UNREACHABLE;
  }
  else if(expr.type().id() == ID_vector)
  {
    const vector_typet &vector_type = to_vector_type(expr.type());

    mp_integer size = numeric_cast_v<mp_integer>(vector_type.size());

    typet index_type = vector_type.size().type();

    result +="(concat";

    // add component-by-component
    for(mp_integer i = 0; i != size; ++i)
    {
      exprt::operandst summands;
      summands.reserve(expr.operands().size());
      for(const auto &op : expr.operands())
        summands.push_back(index_exprt(
          op, from_integer(size - i - 1, index_type), vector_type.subtype()));

      plus_exprt tmp(std::move(summands), vector_type.subtype());

      result +=" ";
      convert_expr(tmp);
    }

    result +=")"; // mk-... or concat
  }
  else
    UNEXPECTEDCASE("unsupported type for +: " + expr.type().id_string());
  return result;
}

std::string convert_mod(const mod_exprt &expr)
{
  std::string result;
  if(expr.type().id()==ID_unsignedbv ||
     expr.type().id()==ID_signedbv)
  {
    if(expr.type().id()==ID_unsignedbv)
      result += "(bvurem ";
    else
      result += "(bvsrem ";

    result += convert_expr(expr.op0());
    result += " ";
    result += convert_expr(expr.op1());
    result += ")";
  }
  else if(expr.type().id()==ID_integer)
  {
    result += "(mod ";
    result += convert_expr(expr.op0());
    result +=" ";
    result += convert_expr(expr.op1());
    result += ")";
  }
  else
    UNEXPECTEDCASE("unsupported type for mod: "+expr.type().id_string());

  return result;
}

// Converting a constant or symbolic rounding mode to SMT-LIB. Only called when
/// use_FPA_theory is enabled
/// \par parameters: The expression representing the rounding mode.
/// \return SMT-LIB output to out.
std::string convert_rounding_mode_FPA(const exprt &expr)
{
  std::string result;
  /* CProver uses the x86 numbering of the rounding-mode
   *   0 == FE_TONEAREST
   *   1 == FE_DOWNWARD
   *   2 == FE_UPWARD
   *   3 == FE_TOWARDZERO
   * These literal values must be used rather than the macros
   * the macros from fenv.h to avoid portability problems.
   */

  if(expr.id()==ID_constant)
  {
    const constant_exprt &cexpr=to_constant_expr(expr);

    mp_integer value = numeric_cast_v<mp_integer>(cexpr);

    if(value==0)
      result += "roundNearestTiesToEven";
    else if(value==1)
      result += "roundTowardNegative";
    else if(value==2)
      result += "roundTowardPositive";
    else if(value==3)
      result += "roundTowardZero";
    else
      INVARIANT_WITH_DIAGNOSTICS(
        false,
        "Rounding mode should have value 0, 1, 2, or 3",
        id2string(cexpr.get_value()));
  }
  else
  {
    std::size_t width=to_bitvector_type(expr.type()).get_width();

    // Need to make the choice above part of the model
    result += "(ite (= (_ bv0 " + integer2string(width) + ") ";
    result += convert_expr(expr);
    result += ") roundNearestTiesToEven ";

    result += "(ite (= (_ bv1 " + integer2string(width) + ") ";
    result += convert_expr(expr);
    result += ") roundTowardNegative ";

    result += "(ite (= (_ bv2 " + integer2string(width) + ") ";
    result += convert_expr(expr);
    result += ") roundTowardPositive ";

    // TODO: add some kind of error checking here
    result += "roundTowardZero";

    result += ")))";
  }
return result;
}

std::string convert_floatbv_plus(const ieee_float_op_exprt &expr)
{
  std::string result;
  const typet &type=expr.type();

  PRECONDITION(
    type.id() == ID_floatbv ||
    (type.id() == ID_complex && type.subtype().id() == ID_floatbv) ||
    (type.id() == ID_vector && type.subtype().id() == ID_floatbv));

  // if(use_FPA_theory)
  {
    if(type.id()==ID_floatbv)
    {
      result += "(fp.add ";
      result += convert_rounding_mode_FPA(expr.rounding_mode());
      result += " ";
      result += convert_expr(expr.lhs());
      result += " ";
      result += convert_expr(expr.rhs());
      result += ")";
    }
    else if(type.id()==ID_complex)
    {
      SMT2_TODO("+ for floatbv complex");
    }
    else if(type.id()==ID_vector)
    {
      SMT2_TODO("+ for floatbv vector");
    }
    else
      INVARIANT_WITH_DIAGNOSTICS(
        false,
        "type should not be one of the unsupported types",
        type.id_string());
  }
  // else
  //   convert_floatbv(expr);
  return result;
}

std::string convert_minus(const minus_exprt &expr)
{
  std::string result;
  if(expr.type().id()==ID_integer)
  {
    result += "(- ";
    result += convert_expr(expr.op0());
    result += " ";
    result += convert_expr(expr.op1());
    result += ")";
  }
  else if(expr.type().id()==ID_unsignedbv ||
     expr.type().id()==ID_signedbv ||
     expr.type().id()==ID_fixedbv)
  {
      result += "(bvsub ";
      result += convert_expr(expr.op0());
      result += " ";
      result += convert_expr(expr.op1());
      result += ")";
  }
  else if(expr.type().id()==ID_floatbv)
  {
    // Floating-point subtraction should have be been converted
    // to ID_floatbv_minus during symbolic execution, adding
    // the rounding mode.  See smt2_convt::convert_floatbv_minus.
    UNREACHABLE;
  }
  else if(expr.type().id()==ID_pointer)
  {
    SMT2_TODO("pointer subtraction");
  }
  else if(expr.type().id()==ID_vector)
  {
    const vector_typet &vector_type=to_vector_type(expr.type());

    mp_integer size = numeric_cast_v<mp_integer>(vector_type.size());

    typet index_type=vector_type.size().type();

    result += "(concat";

    // subtract component-by-component
    for(mp_integer i=0; i!=size; ++i)
    {
      exprt tmp(ID_minus, vector_type.subtype());
      forall_operands(it, expr)
        tmp.copy_to_operands(
          index_exprt(
            *it,
            from_integer(size-i-1, index_type),
            vector_type.subtype()));

      result += " ";
      result += convert_expr(tmp);
    }

    result += ")"; // mk-... or concat
  }
  else
    UNEXPECTEDCASE("unsupported type for -: "+expr.type().id_string());
  return result;
}

std::string convert_floatbv_minus(const ieee_float_op_exprt &expr)
{
  std::string result;
  DATA_INVARIANT(
    expr.type().id() == ID_floatbv,
    "type of ieee floating point expression shall be floatbv");

  // if(use_FPA_theory)
  {
    result += "(fp.sub ";
    result += convert_rounding_mode_FPA(expr.rounding_mode());
    result += " ";
    result += convert_expr(expr.lhs());
    result += " ";
    result += convert_expr(expr.rhs());
    result += ")";
  }
  // else
  //   convert_floatbv(expr);
  return result;
}

std::string convert_div(const div_exprt &expr)
{
  std::string result;
  if(expr.type().id()==ID_unsignedbv ||
     expr.type().id()==ID_signedbv)
  {
    if(expr.type().id()==ID_unsignedbv)
      result += "(bvudiv ";
    else
      result += "(bvsdiv ";

    result += convert_expr(expr.op0());
    result += " ";
    result += convert_expr(expr.op1());
    result += ")";
  }
  else if(expr.type().id()==ID_fixedbv)
  {
    fixedbv_spect spec(to_fixedbv_type(expr.type()));
    std::size_t fraction_bits=spec.get_fraction_bits();

    result += "((_ extract " + integer2string(spec.width-1) + " 0) ";
    result += "(bvsdiv ";

    result += "(concat ";
    result += convert_expr(expr.op0());
    result += " (_ bv0 " + integer2string(fraction_bits) + ")) ";

    result += "((_ sign_extend " + integer2string(fraction_bits)  + ") ";
    result += convert_expr(expr.op1());
    result += ")";

    result += "))";
  }
  else if(expr.type().id()==ID_floatbv)
  {
    // Floating-point division should have be been converted
    // to ID_floatbv_div during symbolic execution, adding
    // the rounding mode.  See smt2_convt::convert_floatbv_div.
    UNREACHABLE;
  }
  else if(expr.type().id()==ID_real)
  {
    result ="(/ ";
    result += convert_expr(expr.op0());
    result += " ";
    result += convert_expr(expr.op1());
    result += ")";

  }
  else
    UNEXPECTEDCASE("unsupported type for /: "+expr.type().id_string());
  return result;
}

std::string convert_floatbv_div(const ieee_float_op_exprt &expr)
{
  std::string result;
  DATA_INVARIANT(
    expr.type().id() == ID_floatbv,
    "type of ieee floating point expression shall be floatbv");

  // if(use_FPA_theory)
  {
    result += "(fp.div ";
    result += convert_rounding_mode_FPA(expr.rounding_mode());
    result += " ";
    result += convert_expr(expr.lhs());
    result += " ";
    result += convert_expr(expr.rhs());
    result += ")";
  }
  // else
  //   convert_floatbv(expr);
  return result;
}

std::string convert_mult(const mult_exprt &expr)
{
  std::string result;
  // re-write to binary if needed
  if(expr.operands().size()>2)
  {
    // strip last operand
    exprt tmp=expr;
    tmp.operands().pop_back();

    // recursive call
    return convert_mult(mult_exprt(tmp, expr.operands().back()));
  }

  INVARIANT(
    expr.operands().size() == 2,
    "expression should have been converted to a variant with two operands");

  if(expr.type().id()==ID_unsignedbv ||
     expr.type().id()==ID_signedbv)
  {
    // Note that bvmul is really unsigned,
    // but this is irrelevant as we chop-off any extra result
    // bits.
    result += "(bvmul ";
    result += convert_expr(expr.op0());
    result += " ";
    result += convert_expr(expr.op1());
    result += ")";
  }
  else if(expr.type().id()==ID_floatbv)
  {
    // Floating-point multiplication should have be been converted
    // to ID_floatbv_mult during symbolic execution, adding
    // the rounding mode.  See smt2_convt::convert_floatbv_mult.
    UNREACHABLE;
  }
  else if(expr.type().id()==ID_fixedbv)
  {
    fixedbv_spect spec(to_fixedbv_type(expr.type()));
    std::size_t fraction_bits=spec.get_fraction_bits();

    result += "((_ extract "
        + integer2string(spec.width+fraction_bits-1) + " "
        + integer2string(fraction_bits) + ") ";

    result += "(bvmul ";

    result += "((_ sign_extend " + integer2string(fraction_bits) + ") ";
    result += convert_expr(expr.op0());
    result += ") ";

    result += "((_ sign_extend " + integer2string(fraction_bits) + ") ";
    result += convert_expr(expr.op1());
    result += ")";

    result += "))"; // bvmul, extract
  }
  else if(expr.type().id()==ID_rational ||
          expr.type().id()==ID_integer ||
          expr.type().id()==ID_real)
  {
    result += "(*";

    forall_operands(it, expr)
    {
      result += " ";
      result += convert_expr(*it);
    }

    result += ")";
  }
  else
    UNEXPECTEDCASE("unsupported type for *: "+expr.type().id_string());
  return result;
}

std::string convert_floatbv_mult(const ieee_float_op_exprt &expr)
{
  std::string result;
  DATA_INVARIANT(
    expr.type().id() == ID_floatbv,
    "type of ieee floating point expression shall be floatbv");

  // if(use_FPA_theory)
  {
    result += "(fp.mul ";
    result += convert_rounding_mode_FPA(expr.rounding_mode());
    result += " ";
    result += convert_expr(expr.lhs());
    result += " ";
   result +=  convert_expr(expr.rhs());
    result += ")";
  }
  // else
  //   convert_floatbv(expr);
  return result;
}

std::string convert_with(const with_exprt &expr)
{
  std::string result;
  // get rid of "with" that has more than three operands

  if(expr.operands().size()>3)
  {
    std::size_t s=expr.operands().size();

    // strip off the trailing two operands
    with_exprt tmp = expr;
    tmp.operands().resize(s-2);

    with_exprt new_with_expr(
      tmp, expr.operands()[s - 2], expr.operands().back());

    // recursive call
    return convert_with(new_with_expr);
  }

  INVARIANT(
    expr.operands().size() == 3,
    "with expression should have been converted to a version with three "
    "operands above");

  const typet &expr_type = expr.type();

  if(expr_type.id()==ID_array)
  {
    const array_typet &array_type=to_array_type(expr_type);

    // if(use_array_theory(expr))
    {
      result += "(store ";
      result += convert_expr(expr.old());
      result += " ";
      result += convert_expr(typecast_exprt(expr.where(), array_type.size().type()));
      result += " ";
      result += convert_expr(expr.new_value());
      result += ")";
    }
  }
  else if(expr_type.id()==ID_bv ||
          expr_type.id()==ID_unsignedbv ||
          expr_type.id()==ID_signedbv)
  {
    // Update bits in a bit-vector. We will use masking and shifts.
    // TODO: SMT2-ify
    SMT2_TODO("SMT2-ify");

#if 0
    result += "(bvor ";
    result += "(band ";

    // the mask to get rid of the old bits
    result += " (bvnot (bvshl";

    result += " (concat";
    result += " (repeat[" + total_width-value_width + "] bv0[1])";
    result += " (repeat[" + value_width + "] bv1[1])";
    result += ")"; // concat

    // shift it to the index
    convert_expr(index_tc);
    result += "))"; // bvshl, bvot

    result += ")"; // bvand

    // the new value
    result += " (bvshl ";
    convert_expr(value);

    // shift it to the index
    convert_expr(index_tc);
    result += ")"; // bvshl

    result += ")"; // bvor
#endif
  }
  else
    UNEXPECTEDCASE(
      "with expects struct, union, or array type, but got "+
      expr.type().id_string());
return result;
}


std::string convert_index(const index_exprt &expr)
{
  std::string result;
  const typet &array_op_type = expr.array().type();

  if(array_op_type.id()==ID_array)
  {
    const array_typet &array_type=to_array_type(array_op_type);

    // if(use_array_theory(expr.array()))
    {
      // if(expr.type().id() == ID_bool && !use_array_of_bool)
      // {
      //   result += "(= ";
      //   result += "(select ";
      //   result += convert_expr(expr.array());
      //   result += " ";
      //   result += convert_expr(typecast_exprt(expr.index(), array_type.size().type()));
      //   result += ")";
      //   result += " #b1 #b0)";
      // }
      // else
      {
        result += "(select ";
        result += convert_expr(expr.array());
        result += " ";
        result += convert_expr(typecast_exprt(expr.index(), array_type.size().type()));
        result += ")";
      }
    }
  }
  else
    INVARIANT(
      false, "index with unsupported array type: " + array_op_type.id_string());
  return result;
}

// std::string convert_member(const member_exprt &expr)
// {
//   std::string result;
//   const member_exprt &member_expr=to_member_expr(expr);
//   const exprt &struct_op=member_expr.struct_op();
//   const typet &struct_op_type = struct_op.type();
//   const irep_idt &name=member_expr.get_component_name();

//   if(struct_op_type.id() == ID_struct || struct_op_type.id() == ID_struct_tag)
//   {
//     const struct_typet &struct_type = to_struct_type(ns.follow(struct_op_type));

//     INVARIANT(
//       struct_type.has_component(name), "struct should have accessed component");

//     {
//       // we extract
//       const std::size_t member_width = boolbv_width(expr.type());
//       const auto member_offset = member_offset_bits(struct_type, name, ns);

//       CHECK_RETURN_WITH_DIAGNOSTICS(
//         member_offset.has_value(), "failed to get struct member offset");

//       result += "((_ extract " + (member_offset.value() + member_width - 1) + " "
//           + member_offset.value() + ") ";
//       result += convert_expr(struct_op);
//       result += ")";
//     }
//   }
//   else if(
//     struct_op_type.id() == ID_union || struct_op_type.id() == ID_union_tag)
//   {
//     std::size_t width=boolbv_width(expr.type());
//     CHECK_RETURN_WITH_DIAGNOSTICS(
//       width != 0, "failed to get union member width");

//     result += unflatten(wheret::BEGIN, expr.type());

//     result += "((_ extract "
//            + (width-1)
//            + " 0) ";
//     result += convert_expr(struct_op);
//     result += ")";

//     result += unflatten(wheret::END, expr.type());
//   }
//   else
//     UNEXPECTEDCASE(
//       "convert_member on an unexpected type "+struct_op_type.id_string());
//   return result;
// }

// std::string flatten2bv(const exprt &expr)
// {
//   std::string result;
//   const typet &type = expr.type();

//   if(type.id()==ID_bool)
//   {
//     result += "(ite ";
//     result += convert_expr(expr); // this returns a Bool
//     result += " #b1 #b0)"; // this is a one-bit bit-vector
//   }
//   else if(type.id()==ID_vector)
//   {
//     result += convert_expr(expr); // already a bv
//   }
//   else if(type.id()==ID_array)
//   {
//     result += convert_expr(expr);
//   }
//   else if(type.id() == ID_struct || type.id() == ID_struct_tag)
//   {
//     result += convert_expr(expr);
//   }
//   else if(type.id()==ID_floatbv)
//   {
//     result += convert_expr(expr);
//   }
//   else
//     result += convert_expr(expr);
//   return result;
// }

std::string unflatten(
  wheret where,
  const typet &type,
  unsigned nesting)
{
  std::string result;
  if(type.id()==ID_bool)
  {
    if(where==wheret::BEGIN)
      result += "(= "; // produces a bool
    else
      result += " #b1)";
  }
  else
  {
    // nop
  }
  return result;
}



std::string convert_type(const typet &type)
{
  std::string result;
  if(type.id()==ID_array)
  {
    const array_typet &array_type=to_array_type(type);
    CHECK_RETURN(array_type.size().is_not_nil());

    result += "(Array ";
    result += convert_type(array_type.size().type());
    result += " ";

    // if(subtype.id()==ID_bool && !use_array_of_bool)
    //   result += "(_ BitVec 1)";
    // else
    result += convert_type(array_type.subtype());

    result += ")";
  }
  else if(type.id()==ID_bool)
  {
    result += "Bool";
  }
  else if(type.id()==ID_code)
  {
    // These may appear in structs.
    // We replace this by "Bool" in order to keep the same
    // member count.
    result += "Bool";
  }
  // else if(type.id() == ID_union || type.id() == ID_union_tag)
  // {
  //   std::size_t width=boolbv_width(type);
  //   CHECK_RETURN_WITH_DIAGNOSTICS(width != 0, "failed to get width of union");

  //   result += "(_ BitVec " + width + ")";
  // }
  // else if(type.id()==ID_pointer)
  // {
  //   result += "(_ BitVec "
  //       + boolbv_width(type) + ")";
  // }
  else if(type.id()==ID_bv ||
          type.id()==ID_fixedbv ||
          type.id()==ID_unsignedbv ||
          type.id()==ID_signedbv ||
          type.id()==ID_c_bool)
  {
    result += "(_ BitVec "
        + integer2string(to_bitvector_type(type).get_width()) + ")";
  }
  else if(type.id()==ID_c_enum)
  {
    // these have a subtype
    result += "(_ BitVec "
        + integer2string(to_bitvector_type(type.subtype()).get_width()) + ")";
  }
  else if(type.id()==ID_floatbv)
  {
    const floatbv_typet &floatbv_type=to_floatbv_type(type);

    // if(use_FPA_theory)
      result += "(_ FloatingPoint "
          + integer2string(floatbv_type.get_e()) + " "
          + integer2string(floatbv_type.get_f() + 1) + ")";
    // else
    //   result += "(_ BitVec "
    //       + floatbv_type.get_width() + ")";
  }
  else if(type.id()==ID_rational ||
          type.id()==ID_real)
    result += "Real";
  else if(type.id()==ID_integer)
    result += "Int";
  // else if(type.id()==ID_complex)
  // {
  //   {
  //     std::size_t width=boolbv_width(type);
  //     CHECK_RETURN_WITH_DIAGNOSTICS(
  //       width != 0, "failed to get width of complex");

  //     result += "(_ BitVec " + width + ")";
  //   }
  // }
  else if(type.id()==ID_mathematical_function)
  {
    result += "(-> ";
    auto &func=to_mathematical_function_type(type);
    for(const auto &op: func.domain())
      result += convert_type(op);
    result += convert_type(func.codomain()) ;
    result += ")"; 
  }
  else
  {
    UNEXPECTEDCASE("unsupported type: "+type.id_string());
  }
  return result;
}

std::string flatten2bv(const exprt &expr)
{
  std::string result;
  const typet &type = expr.type();

  if(type.id()==ID_bool)
  {
    result += "(ite ";
    result += convert_expr(expr); // this returns a Bool
    result += " #b1 #b0)"; // this is a one-bit bit-vector
  }
  else if(type.id()==ID_array)
  {
    result += convert_expr(expr);
  }
  else if(type.id() == ID_struct || type.id() == ID_struct_tag)
  {
    result += convert_expr(expr);
  }
  else
    result += convert_expr(expr);
  return result;
}

std::string convert_typecast(const typecast_exprt &expr)
{
  std::string result;
  const exprt &src = expr.op();

  typet dest_type = expr.type();
  typet src_type = src.type();

  if(dest_type.id()==ID_bool)
  {
    // this is comparison with zero
    if(src_type.id()==ID_signedbv ||
       src_type.id()==ID_unsignedbv ||
       src_type.id()==ID_c_bool ||
       src_type.id()==ID_fixedbv ||
       src_type.id()==ID_pointer ||
       src_type.id()==ID_integer)
    {
      result += "(not (= ";
      result +=convert_expr(src);
      result += " ";
      result +=convert_expr(from_integer(0, src_type));
      result += "))";
    }
    else if(src_type.id()==ID_floatbv)
    {
      // if(use_FPA_theory)
      {
        result += "(not (fp.isZero ";
        result +=convert_expr(src);
        result += "))";
      }

    }
    else
    {
      UNEXPECTEDCASE("TODO typecast1 "+src_type.id_string()+" -> bool");
    }
  }
  else if(dest_type.id()==ID_unsignedbv ||
          dest_type.id()==ID_signedbv ||
          dest_type.id()==ID_fixedbv ||
          dest_type.id()==ID_unsignedbv )
  {
    if(src_type.id()==ID_bool)
    {
      result += "(ite ";
      result +=convert_expr(src);
      result += " ";
      result +=convert_expr(from_integer(1, dest_type));
      result +=" ";
      result +=convert_expr(from_integer(0, dest_type));
      result += " )";
    }
  }
  else if(dest_type.id()==ID_floatbv)
  {
    // Typecast from integer to floating-point should have be been
    // converted to ID_floatbv_typecast during symbolic execution,
    // adding the rounding mode.  See
    // smt2_convt::convert_floatbv_typecast.
    // The exception is bool and c_bool to float.
    const auto &dest_floatbv_type = to_floatbv_type(dest_type);

    if(src_type.id()==ID_bool)
    {
      constant_exprt val(irep_idt(), dest_type);

      ieee_floatt a(dest_floatbv_type);

      mp_integer significand;
      mp_integer exponent;

      result += "(ite ";
      result += convert_expr(src);
      result += " ";

      significand = 1;
      exponent = 0;
      a.build(significand, exponent);
      val.set_value(integer2bvrep(a.pack(), a.spec.width()));

      result += convert_constant(val);
      result += " ";

      significand = 0;
      exponent = 0;
      a.build(significand, exponent);
      val.set_value(integer2bvrep(a.pack(), a.spec.width()));

      result += convert_constant(val);
      result += ")";
    }
    else if(src_type.id() == ID_bv)
    {
      if(to_bv_type(src_type).get_width() != dest_floatbv_type.get_width())
      {
        UNEXPECTEDCASE("Typecast bv -> float with wrong width");
      }

      // if(use_FPA_theory)
      {
        result += "((_ to_fp " + integer2string(dest_floatbv_type.get_e()) + " "
            + integer2string(dest_floatbv_type.get_f() + 1) + ") ";
        result += convert_expr(src);
        result += ')';
      }
    }
    else
      UNEXPECTEDCASE("Unknown typecast "+src_type.id_string()+" -> float");
  }
  else if(dest_type.id()==ID_integer)
  {
    if(src_type.id()==ID_bool)
    {
      result += "(ite ";
      result += convert_expr(src);
      result +=" 1 0)";
    }
    else
      UNEXPECTEDCASE("Unknown typecast "+src_type.id_string()+" -> integer");
  }
  else
    UNEXPECTEDCASE(
      "TODO typecast8 "+src_type.id_string()+" -> "+dest_type.id_string());
  return result;
}

std::string convert_floatbv_typecast(const floatbv_typecast_exprt &expr)
{
  std::string result;
  const exprt &src=expr.op();
  // const exprt &rounding_mode=expr.rounding_mode();
  const typet &src_type=src.type();
  const typet &dest_type=expr.type();

  if(dest_type.id()==ID_floatbv)
  {
    if(src_type.id()==ID_floatbv)
    {
      // float to float

      /* ISO 9899:1999
       * 6.3.1.5 Real floating types
       * 1 When a float is promoted to double or long double, or a
       * double is promoted to long double, its value is unchanged.
       *
       * 2 When a double is demoted to float, a long double is
       * demoted to double or float, or a value being represented in
       * greater precision and range than required by its semantic
       * type (see 6.3.1.8) is explicitly converted to its semantic
       * type, if the value being converted can be represented
       * exactly in the new type, it is unchanged. If the value
       * being converted is in the range of values that can be
       * represented but cannot be represented exactly, the result
       * is either the nearest higher or nearest lower representable
       * value, chosen in an implementation-defined manner. If the
       * value being converted is outside the range of values that
       * can be represented, the behavior is undefined.
       */

      const floatbv_typet &dst=to_floatbv_type(dest_type);

      // if(use_FPA_theory)
      {
        result += "((_ to_fp " + integer2string(dst.get_e()) + " "
            + integer2string(dst.get_f() + 1 )+ ") ";
        result += convert_rounding_mode_FPA(expr.op1());
        result += " ";
        result += convert_expr(src);
        result += ")";
      }

    }
    else if(src_type.id()==ID_unsignedbv)
    {
      // unsigned to float

      /* ISO 9899:1999
       * 6.3.1.4 Real floating and integer
       * 2 When a value of integer type is converted to a real
       * floating type, if the value being converted can be
       * represented exactly in the new type, it is unchanged. If the
       * value being converted is in the range of values that can be
       * represented but cannot be represented exactly, the result is
       * either the nearest higher or nearest lower representable
       * value, chosen in an implementation-defined manner. If the
       * value being converted is outside the range of values that can
       * be represented, the behavior is undefined.
       */

      const floatbv_typet &dst=to_floatbv_type(dest_type);

      // if(use_FPA_theory)
      {
        result += "((_ to_fp_unsigned " + integer2string(dst.get_e()) + " "
            + integer2string(dst.get_f() + 1 )+ ") ";
        result += convert_rounding_mode_FPA(expr.op1());
        result += " ";
        result += convert_expr(src);
        result += ")";
      }
      // else
      //   result += convert_floatbv(expr);
    }
    else if(src_type.id()==ID_signedbv)
    {
      // signed to float

      const floatbv_typet &dst=to_floatbv_type(dest_type);

      // if(use_FPA_theory)
      {
        result += "((_ to_fp " +integer2string(dst.get_e()) + " "
            + integer2string(dst.get_f() + 1 )+ ") ";
        result += convert_rounding_mode_FPA(expr.op1());
        result += " ";
        result += convert_expr(src);
        result += ")";
      }
      // else
      //   convert_floatbv(expr);
    }
    else if(src_type.id()==ID_real)
    {
      // if(use_FPA_theory)
      {
        const floatbv_typet &dst=to_floatbv_type(dest_type);
        result += "((_ to_fp " + integer2string(dst.get_e()) + " " +
            integer2string(dst.get_f() + 1 )+ ") ";
        result += convert_rounding_mode_FPA(expr.op1());
        result += " ";
        result += convert_expr(src);
        result += ")";
      }
      // else
      //   UNEXPECTEDCASE(
      //   "TODO typecast11 "+src_type.id_string()+" -> "+dest_type.id_string());    
    }
    else
      UNEXPECTEDCASE(
        "TODO typecast11 "+src_type.id_string()+" -> "+dest_type.id_string());
  }
  else if(dest_type.id()==ID_signedbv)
  {
    // if(use_FPA_theory)
    {
      std::size_t dest_width=to_signedbv_type(dest_type).get_width();
      result += "((_ fp.to_sbv " + integer2string(dest_width) + ") ";
      result += convert_rounding_mode_FPA(expr.op1());
      result += " ";
      result += convert_expr(src);
      result += ")";
    }
  }
  else if(dest_type.id()==ID_unsignedbv)
  {
    // if(use_FPA_theory)
    {
      std::size_t dest_width=to_unsignedbv_type(dest_type).get_width();
      result += "((_ fp.to_ubv " + integer2string(dest_width) + ") ";
      result += convert_rounding_mode_FPA(expr.op1());
      result += " ";
      result += convert_expr(src);
      result += ")";
    }

  }
  else
  {
    UNEXPECTEDCASE(
      "TODO typecast12 "+src_type.id_string()+" -> "+dest_type.id_string());
  }
  return result;
}