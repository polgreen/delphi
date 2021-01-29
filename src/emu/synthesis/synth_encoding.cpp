#include <util/std_types.h>
#include <util/config.h>
#include <util/bv_arithmetic.h>

#include "synth_encoding.h"
#include "../expr2sygus.h"
#include <algorithm>
#include <iostream>

typet promotion(const typet &t0, const typet &t1)
{
  // same?
  if(t0==t1)
    return t0;

  // one is boolean?
  if(t0.id()==ID_bool)
    return t1;

  if(t1.id()==ID_bool)
    return t0;

  // same encoding but different width
  if(t0.id()==ID_signedbv && t1.id()==ID_signedbv)
  {
    auto t0_width=to_signedbv_type(t0).get_width();
    auto t1_width=to_signedbv_type(t1).get_width();
    return t0_width>=t1_width?t0:t1;
  }
  else if(t0.id()==ID_unsignedbv && t1.id()==ID_unsignedbv)
  {
    auto t0_width=to_unsignedbv_type(t0).get_width();
    auto t1_width=to_unsignedbv_type(t1).get_width();
    return t0_width>=t1_width?t0:t1;
  }
  else
    return t0;
}

exprt promotion(const exprt &expr, const typet &t)
{
  if(expr.type()==t)
    return expr;

  return typecast_exprt(expr, t);
}

typet e_datat::compute_word_type()
{
  typet result=return_type;

  for(const auto & t : parameter_types)
    result=promotion(result, t);

  return result;
}

void e_datat::setup(
  const function_application_exprt &e,
  const std::size_t program_size,
  const bool _enable_bitwise)
{
  if(setup_done) return;
  setup_done=true;

  enable_bitwise=_enable_bitwise;

  function_symbol=to_symbol_expr(e.function());
  const irep_idt &identifier=function_symbol.get_identifier();

  return_type=e.type();

  const auto &arguments=e.arguments();
  parameter_types.resize(arguments.size());
  for(std::size_t i=0; i<parameter_types.size(); i++)
    parameter_types[i]=arguments[i].type();

  word_type=compute_word_type();

  for(auto it(begin(literals)); it != end(literals);)
    if(word_type!=it->type())
      it=literals.erase(it);
    else
      ++it;

  instructions.reserve(program_size);
  for(std::size_t pc=0; pc<program_size; pc++)
  {
    instructions.push_back(instructiont(pc));
    auto &instruction=instructions[pc];

    // constant -- hardwired default, not an option
    irep_idt const_val_id=id2string(identifier)+"_"+std::to_string(pc)+"_cval";
    instruction.constant_val=symbol_exprt(const_val_id, word_type);

    // one of the arguments or constants
    for(std::size_t i=0; i<arguments.size()+literals.size(); i++)
    {
      irep_idt param_sel_id=id2string(identifier)+"_"+
               std::to_string(pc)+"_p"+std::to_string(i)+"sel";
      auto &option=instruction.add_option(param_sel_id);
      option.kind=instructiont::optiont::PARAMETER;
      option.parameter_number=i;
    }

    // a binary operation

    static const irep_idt ops[]=
      { ID_plus, ID_minus, ID_shl, ID_bitand, ID_bitor, ID_bitxor,
        ID_le, ID_lt, ID_equal, ID_notequal, "max", "min", ID_div, ID_lshr, };
   // static const irep_idt ops[]=
     ///     { ID_plus, ID_minus, ID_ashr, ID_shr, ID_bitor };

    std::size_t binary_option_index=0;

    for(const auto &operation : ops)
    {
      if(!enable_bitwise || word_type.id()==ID_integer)
        if(operation==ID_lshr ||
           operation==ID_shl ||
           operation==ID_bitand ||
           operation==ID_bitor ||
           operation==ID_bitxor)
          continue;

      if((word_type.id()!=ID_unsignedbv &&
          word_type.id()!=ID_signedbv) || !enable_division)
        if(operation==ID_div)
          continue;

      for(std::size_t operand0=0; operand0<pc; operand0++)
        for(std::size_t operand1=0; operand1<pc; operand1++)
        {
          // there is usually no point applying an operation to two
          // identical operands, with the exception of ID_plus, which
          // produces 2*x
          if(operand0==operand1 && operation!=ID_plus)
            continue;

          // many operators are commutative, no need
          // to have both orderings
          if(operation==ID_plus ||
             operation==ID_bitand ||
             operation==ID_bitor ||
             operation==ID_bitxor ||
             operation==ID_equal ||
             operation==ID_notequal ||
             operation=="max" ||
             operation=="min")
          {
            if(operand0>operand1)
              continue;
          }

          irep_idt final_operation=operation;

          if(word_type.id()==ID_bool)
          {
            if(operation==ID_plus ||
               operation==ID_minus ||
               operation==ID_lshr ||
               operation==ID_shl ||
               operation==ID_lt ||
               operation==ID_le ||
               operation==ID_notequal || // we got bitxor
               operation=="max" ||
               operation=="min" ||
               operation==ID_div)
              continue;

            if(operation==ID_bitand)
              final_operation=ID_and;
            else if(operation==ID_bitor)
              final_operation=ID_or;
            else if(operation==ID_bitxor)
              final_operation=ID_xor;
          }

          irep_idt sel_id=id2string(identifier)+"_"+
                   std::to_string(pc)+"_b"+
                   std::to_string(binary_option_index)+"sel";

          auto &option=instruction.add_option(sel_id);
          option.operand0=operand0;
          option.operand1=operand1;
          option.operation=final_operation;

          if(final_operation==ID_le ||
             final_operation==ID_lt ||
             final_operation==ID_equal ||
             final_operation==ID_notequal)
            option.kind=instructiont::optiont::BINARY_PREDICATE;
          else
            option.kind=instructiont::optiont::BINARY;

          binary_option_index++;
        }
    }

    std::size_t ternary_option_index=0;
    // trinary operator, if-then-else
    for(std::size_t operand0=0; operand0<pc; operand0++)
      for(std::size_t operand1=0; operand1<pc; operand1++)
        for(std::size_t operand2=0; operand2<pc; operand2++)
        {
          // no point using if-then-else if operand 1 and operand 2
          // are the same
          if(operand1==operand2)
            continue;

          if(operand0==operand1 || operand0==operand2)
            continue;

          irep_idt sel_id=id2string(identifier)+"_"+
                   std::to_string(pc)+"_t"+
                   std::to_string(ternary_option_index)+"ite_sel";


          auto &option=instruction.add_option(sel_id);
          option.operand0=operand0;
          option.operand1=operand1;
          option.operand2=operand2;
          option.operation=ID_if;
          option.kind=instructiont::optiont::ITE;

          ternary_option_index++;
        }

  }
}

if_exprt e_datat::instructiont::chain(
  const symbol_exprt &selector,
  const exprt &expr_true,
  const exprt &expr_false)
{
  return if_exprt(
    selector,
    expr_true,
    expr_false);
}

exprt e_datat::instructiont::constraint(
  const typet &word_type,
  const std::vector<exprt> &arguments,
  const std::vector<exprt> &results)
{
  // constant, which is last resort
  exprt result_expr=constant_val;

  for(const auto &option : options)
  {
    switch(option.kind)
    {
    case optiont::PARAMETER:
      {
        exprt promoted_arg=
          promotion(arguments[option.parameter_number], word_type);
        result_expr=chain(option.sel, promoted_arg, result_expr);
      }
      break;

    case optiont::UNARY:
      // TBD
      break;

    case optiont::BINARY: // a binary operation
      {
        assert(option.operand0<results.size());
        assert(option.operand1<results.size());

        const auto &op0=results[option.operand0];
        const auto &op1=results[option.operand1];

        if(option.operation=="max" ||
           option.operation=="min")
        {
          irep_idt op=option.operation=="max"?ID_ge:ID_le;
          binary_predicate_exprt rel(op0, op, op1);
          if_exprt if_expr(rel, op0, op1);
          result_expr=chain(option.sel, if_expr, result_expr);
        }
        else if(option.operation=="ID_div")
        {
          // if op1 is zero, smt division returns 1111
          equal_exprt op_divbyzero(op1, constant_exprt("0", op1.type()));

          binary_exprt binary_expr(op0, option.operation, op1);

          bv_spect spec(op0.type());
          if_exprt if_expr(op_divbyzero, constant_exprt(integer2string(spec.max_value()), op0.type()),
              binary_expr);
          result_expr = chain(option.sel, if_expr, result_expr);
        }
        else if(option.operation=="ID_lshr")
        {
          // shift operator
          lshr_exprt shift_expr(op0, op1);
                  shift_expr.type()=op0.type();

         binary_predicate_exprt shift_greater_than_width(
           op1, 
           ID_ge,
           constant_exprt(integer2string(to_unsignedbv_type(op0.type()).get_width()),op0.type()));
     
         if_exprt if_expr(shift_greater_than_width, constant_exprt("0", op0.type()), shift_expr);
         result_expr=chain(option.sel, if_expr, result_expr);
        }
        else
        {
          binary_exprt binary_expr(op0, option.operation, op1);
          result_expr=chain(option.sel, binary_expr, result_expr);
        }
      }
      break;

    case optiont::BINARY_PREDICATE: // a predicate
      {
        assert(option.operand0<results.size());
        assert(option.operand1<results.size());

        const auto &op0=results[option.operand0];
        const auto &op1=results[option.operand1];

        binary_exprt binary_expr(op0, option.operation, op1, bool_typet());
        exprt promoted=promotion(binary_expr, word_type);
        result_expr=chain(option.sel, promoted, result_expr);
      }
      break;
    case optiont::ITE: // if-then-else
    {
      assert(option.operand0<results.size());
      assert(option.operand1<results.size());
      assert(option.operand2<results.size());

      const auto &op0=results[option.operand0];
      const auto &op1=results[option.operand1];
      const auto &op2=results[option.operand2];

      exprt op0_conv=
          (word_type.id()==ID_bool)?op0:
          typecast_exprt(op0, bool_typet());

      if_exprt if_expr(op0_conv, op1, op2);
      result_expr=chain(option.sel, if_expr, result_expr);
    }
    break;

    case optiont::NONE:
      std::cout<<"error: option kind: " << option.kind<<std::endl;
      UNREACHABLE;
    }
  }

  return result_expr;
}

std::size_t e_datat::instance_number(const argumentst &arguments)
{
  const auto res=instances.insert(
    std::pair<argumentst, std::size_t>(arguments, instances.size()));

  return res.first->second;
}

exprt e_datat::result(const argumentst &arguments)
{
  // find out which instance this is
  std::size_t instance_number=this->instance_number(arguments);

  std::vector<exprt> results;
  results.resize(instructions.size(), nil_exprt());

  constraints.clear();

  const irep_idt &identifier=function_symbol.get_identifier();

  for(std::size_t pc=0; pc<instructions.size(); pc++)
  {
    argumentst args_with_consts(arguments);
    copy(begin(literals), end(literals), back_inserter(args_with_consts));
    exprt c=instructions[pc].constraint(word_type, args_with_consts, results);

    // results vary by instance
    irep_idt result_identifier=
      id2string(identifier)+"_inst"+std::to_string(instance_number)+
      "_result_"+std::to_string(pc);

    results[pc]=symbol_exprt(result_identifier, c.type());

    constraints.push_back(equal_exprt(results[pc], c));
  }

  assert(!results.empty());

  return promotion(results.back(), return_type);
}

exprt e_datat::get_function(
  const decision_proceduret &solver,
  bool constant_variables) const
{
  assert(!instructions.empty());

  std::vector<exprt> results;
  results.resize(instructions.size(), nil_exprt());

  for(std::size_t pc=0; pc<instructions.size(); pc++)
  {
    const auto &instruction=instructions[pc];
    exprt &result=results[pc];
    result=nil_exprt();

    // we now go _backwards_ through the options, as we've
    // built the ite inside-out

    for(instructiont::optionst::const_reverse_iterator
        o_it=instruction.options.rbegin();
        result.is_nil() && o_it!=instruction.options.rend();
        o_it++)
    {
      if(solver.get(o_it->sel).is_true())
      {
        switch(o_it->kind)
        {
        case instructiont::optiont::PARAMETER: // a parameter
          {
            const size_t num_params=parameter_types.size();
            if(o_it->parameter_number < num_params)
            {
              irep_idt p_identifier="synth::parameter"+
                       std::to_string(o_it->parameter_number);
              result=promotion(
                symbol_exprt(p_identifier, parameter_types[o_it->parameter_number]),
                word_type);
            }
            else // Constant
            {
              const size_t const_index=o_it->parameter_number - num_params;
              result=*next(begin(literals), const_index);
            }
          }
          break;

        case instructiont::optiont::UNARY:
          // TBD
          break;

        case instructiont::optiont::BINARY:
          {
            const auto &binary_op=*o_it;

            assert(binary_op.operand0<results.size());
            assert(binary_op.operand1<results.size());

            exprt op0=results[binary_op.operand0];
            exprt op1=results[binary_op.operand1];

            if(binary_op.operation=="max")
            {
              binary_predicate_exprt rel(op0, ID_ge, op1);
              result=if_exprt(rel, op0, op1);
            }
            else if(binary_op.operation=="min")
            {
              binary_predicate_exprt rel(op0, ID_le, op1);
              result=if_exprt(rel, op0, op1);
            }
            else
            {
              result=binary_exprt(
                op0,
                binary_op.operation,
                op1);
            }
          }
          break;

        case instructiont::optiont::BINARY_PREDICATE:
          {
            const auto &binary_op=*o_it;

            assert(binary_op.operand0<results.size());
            assert(binary_op.operand1<results.size());

            result=binary_exprt(
              results[binary_op.operand0],
              binary_op.operation,
              results[binary_op.operand1],
              bool_typet());

            result=promotion(result, word_type);
          }
          break;

        case instructiont::optiont::ITE:
          {
            const auto &ite_op = *o_it;
            assert(ite_op.operand0 < results.size());
            assert(ite_op.operand1 < results.size());
            assert(ite_op.operand2 < results.size());

            exprt op0 = results[ite_op.operand0];

            exprt op0_conv =
              word_type.id() == ID_bool?op0 :
                  typecast_exprt(op0, bool_typet());

            result = if_exprt(op0_conv, results[ite_op.operand1],
              results[ite_op.operand2]);
          }
          break;

        case instructiont::optiont::NONE:
          UNREACHABLE;
        }
      }
    }

    // constant, this is the last resort when none of the
    // selectors is true
    if(result.is_nil())
    {
      if(constant_variables)
        result=instruction.constant_val;
      else
        result=solver.get(instruction.constant_val);
    }
  }

  return promotion(results.back(), return_type);
}

exprt synth_encodingt::operator()(const exprt &expr)
{
  if(expr.id()==ID_function_application)
  {
    auto tmp=to_function_application_expr(expr);

    auto &func_id = to_symbol_expr(tmp.function()).get_identifier();
    if(synth_funs.find(func_id) == synth_funs.end())
    {
      exprt tmp = expr;
      for(auto &op : tmp.operands())
        op =(*this)(op); // recursive call
      return tmp;
    }
    // apply recursively to arguments
    for(auto &op : tmp.arguments())
      op=(*this)(op);

    e_datat &e_data=e_data_map[to_symbol_expr(tmp.function())];
    if(e_data.word_type.id().empty())
      e_data.literals=literals;
    exprt final_result=e_data(
      tmp, program_size, enable_bitwise, enable_division);

    for(const auto &c : e_data.constraints)
    {
      constraints.push_back(c);
    }

    return final_result;
  }
  else if(expr.id()==ID_symbol)
  {
    // add the suffix
    symbol_exprt tmp=to_symbol_expr(expr);
    tmp.set_identifier(id2string(tmp.get_identifier())+suffix);
    return std::move(tmp);
  }
  else if(expr.id()==ID_nondet_symbol)
  {
    // add the suffix
    nondet_symbol_exprt tmp=to_nondet_symbol_expr(expr);
    irep_idt identifier=tmp.get_identifier();
    tmp.set_identifier(id2string(identifier)+suffix);
    return std::move(tmp);
  }
  else
  {
    exprt tmp=expr;

    for(auto &op : tmp.operands())
      op=(*this)(op); // recursive call

    return tmp;
  }
}

solutiont synth_encodingt::get_solution(
  const decision_proceduret &solver) const
{
  solutiont result;

  for(const auto &it : e_data_map)
  {
    result.functions[it.first]=
      it.second.get_function(solver, false);
  }

  return result;
}

void synth_encodingt::clear()
{
  e_data_map.clear();
  constraints.clear();
}
