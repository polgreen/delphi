#include "sygus_parser.h"

#include <util/bv_arithmetic.h>
#include <util/std_types.h>
#include <util/std_expr.h>
#include <util/replace_symbol.h>
#include <util/arith_tools.h>

#include <cctype>
#include <cassert>
#include <fstream>

void sygus_parsert::replace_higher_order_logic(exprt &expr)
{
  if(expr.id()==ID_function_application)
  {
    for(auto &arg: to_function_application_expr(expr).arguments())
    {
      if(arg.type().id()==ID_mathematical_function)
      {
        std::string new_id = "_synthbool_"+ id2string(to_symbol_expr(arg).get_identifier());
        arg = symbol_exprt(new_id, bool_typet());
      }
    }
    auto &func = to_symbol_expr(to_function_application_expr(expr).function());
    for(auto &d: to_mathematical_function_type(func.type()).domain())
    {
      if(d.id()==ID_mathematical_function)
        d = bool_typet();
    }
  }
  for(auto &op: expr.operands())
    replace_higher_order_logic(op);
}

void sygus_parsert::replace_higher_order_logic()
{
  for(auto &c: constraints)
    replace_higher_order_logic(c);

  for(auto &a: assumptions)
    replace_higher_order_logic(a);

  for(auto &gen: oracle_constraint_gens)
    replace_higher_order_logic(gen.constraint);

  for(auto &gen: oracle_assumption_gens)
    replace_higher_order_logic(gen.constraint);
}

oracle_constraint_gent
sygus_parsert::oracle_signature()
{
  if(next_token() != smt2_tokenizert::SYMBOL)
      throw error("expected a symbol after define-fun");

  const irep_idt binary_name = smt2_tokenizer.get_buffer();
  std::vector<symbol_exprt> inputs;
  std::vector<symbol_exprt> outputs;

  // get input symbols
  if(next_token() != smt2_tokenizert::OPEN)
    throw error("expected '(' at beginning of oracle input symbols");

  if(smt2_tokenizer.peek() == smt2_tokenizert::CLOSE)
  {
    // no inputs
  }
  
  while(smt2_tokenizer.peek() != smt2_tokenizert::CLOSE)
  {
    if(next_token() != smt2_tokenizert::OPEN)
      throw error("expected '(' at beginning of parameter");

    if(next_token() != smt2_tokenizert::SYMBOL)
      throw error("expected symbol in parameter");

    irep_idt id = smt2_tokenizer.get_buffer();
    typet param_sort = sort();
    // TODO: check that the id exists already?
    if(id_map.find(id)==id_map.end())
      throw error("input to oracle must be a known id");

    inputs.push_back(symbol_exprt(id, param_sort));

    if(next_token() != smt2_tokenizert::CLOSE)
      throw error("expected ')' at end of input parameter");
  }

  next_token(); // eat the ')'
  // get output symbols
  if(next_token() != smt2_tokenizert::OPEN)
    throw error("expected '(' at beginning of oracle output symbols");

  if(smt2_tokenizer.peek() == smt2_tokenizert::CLOSE)
  {
    // no outputs
    next_token(); // eat the ')'
  }

  while(smt2_tokenizer.peek() != smt2_tokenizert::CLOSE)
  {
    if(next_token() != smt2_tokenizert::OPEN)
      throw error("expected '(' at beginning of parameter");

    if(next_token() != smt2_tokenizert::SYMBOL)
      throw error("expected symbol in parameter");

    irep_idt id = smt2_tokenizer.get_buffer();
    typet param_sort = sort();
    outputs.push_back(symbol_exprt(id, param_sort));

    // these are allowed to be new ids
    if(id_map.find(id)==id_map.end())
      add_unique_id(id, symbol_exprt(id, param_sort));

    if(next_token() != smt2_tokenizert::CLOSE)
      throw error("expected ')' at end of input parameter");
  }
  next_token(); // eat the ')'

  // get constraint
  exprt constraint = expression();
  return oracle_constraint_gent(binary_name,inputs, outputs, constraint);
}

void sygus_parsert::setup_commands()
{
  commands["set-logic"] = [this] {
    if(smt2_tokenizer.next_token()!=smt2_tokenizert::SYMBOL)
      throw error("expected a symbol after set-logic");

    logic=smt2_tokenizer.get_buffer();
  };

  commands["synth-fun"] = [this] {
    if(smt2_tokenizer.next_token()!=smt2_tokenizert::SYMBOL)
      throw error("expected a symbol after synth-fun");

    // save the renaming map
    renaming_mapt old_renaming_map = renaming_map;
    irep_idt id=smt2_tokenizer.get_buffer();

    if(id_map.find(id)!=id_map.end())
      throw error() << "function `" << id << "' declared twice";

    auto signature=(id=="inv-f")?
      inv_function_signature() : function_signature_definition();

    // restore renamings
    std::swap(renaming_map, old_renaming_map);

    // we'll tweak the type in case there are no parameters
    if(signature.type.id() != ID_mathematical_function)
    {
      // turn into () -> signature.type
      signature.type = mathematical_function_typet({}, signature.type);
    }

    NTDef_seq();

    auto f_it = id_map.emplace(
      std::piecewise_construct,
      std::forward_as_tuple(id),
      std::forward_as_tuple(idt::VARIABLE, nil_exprt()));

    f_it.first->second.type = signature.type;
    f_it.first->second.parameters = signature.parameters;

    synth_fun_set.insert(symbol_exprt(id, signature.type));
  };

  commands["synth-inv"] = commands["synth-fun"];

  commands["declare-var"]=[this]{
    const auto s = smt2_tokenizer.get_buffer();

    if(next_token() != smt2_tokenizert::SYMBOL)
      throw error() << "expected a symbol after " << s;

    irep_idt id = smt2_tokenizer.get_buffer();
    auto type = sort();

    add_unique_id(id, exprt(ID_nil, type));
    if(type.id()!=ID_mathematical_function)
      variable_set.insert(symbol_exprt(id, type));
  };

  commands["declare-primed-var"] = [this] {
    if(smt2_tokenizer.next_token()!=smt2_tokenizert::SYMBOL)
      throw error("expected a symbol after declare-primed-var");

    irep_idt id = smt2_tokenizer.get_buffer();
    irep_idt id_prime = smt2_tokenizer.get_buffer()+"!";
    auto type = sort();

    if(id_map.find(id)!=id_map.end())
      throw error("variable declared twice");

    if(id_map.find(id_prime)!=id_map.end())
      throw error("variable declared twice");

    id_map.emplace(
      std::piecewise_construct,
      std::forward_as_tuple(id),
      std::forward_as_tuple(idt::VARIABLE, exprt(ID_nil, type)));

    id_map.emplace(
      std::piecewise_construct,
      std::forward_as_tuple(id_prime),
      std::forward_as_tuple(idt::VARIABLE, exprt(ID_nil, type)));
  };

  commands["constraint"] = [this] {
    constraints.push_back(expression());
  };

  commands["assume"] = [this] {
    assumptions.push_back(expression());
  };

  commands["oracle-constraint"]=[this]{
  
    // save the renaming map
    renaming_mapt old_renaming_map = renaming_map;
    // get constraint
    oracle_constraint_gent constraint = oracle_signature();
    oracle_constraint_gens.push_back(constraint);
    renaming_map = old_renaming_map;    
  };

  commands["oracle-assumption"]=[this]{
        // save the renaming map
    renaming_mapt old_renaming_map = renaming_map;
    // get constraint
    oracle_constraint_gent assumption = oracle_signature();
    oracle_assumption_gens.push_back(assumption);
    renaming_map = old_renaming_map;    
  };

  commands["inv-constraint"] = [this] {
    ignore_command();
    generate_invariant_constraints();
  };

  commands["set-options"] = [this] {
    ignore_command();
  };

  commands["check-synth"] = [this] {
    action="check-synth";
  };
}

sygus_parsert::signature_with_parameter_idst sygus_parsert::inv_function_signature()
{
  if(smt2_tokenizer.next_token()!=smt2_tokenizert::OPEN)
    throw error("expected '(' at beginning of signature");

  mathematical_function_typet::domaint domain;
  std::vector<irep_idt> parameter_ids;

  while(smt2_tokenizer.peek()!=smt2_tokenizert::CLOSE)
  {
    if(smt2_tokenizer.next_token()!=smt2_tokenizert::OPEN)
      throw error("expected '(' at beginning of parameter");

    if(smt2_tokenizer.next_token()!=smt2_tokenizert::SYMBOL)
      throw error("expected symbol in parameter");

    const irep_idt id=smt2_tokenizer.get_buffer();
    const auto parameter_type = sort();
    domain.push_back(parameter_type);
    parameter_ids.push_back(id);

    if(smt2_tokenizer.next_token()!=smt2_tokenizert::CLOSE)
      throw error("expected ')' at end of parameter");
  }

  smt2_tokenizer.next_token(); // eat the ')'

  auto type = mathematical_function_typet(domain, bool_typet());
  return signature_with_parameter_idst(type, parameter_ids);
}

function_application_exprt sygus_parsert::apply_function_to_variables(
  invariant_constraint_functiont function_type,
  invariant_variablet var_use)
{
  std::string suffix;
  if(var_use == PRIMED)
    suffix = "!";

  std::string id;
  switch(function_type)
  {
  case PRE:
    id = "pre-f";
    break;
  case INV:
    id = "inv-f";
    break;
  case TRANS:
    id = "trans-f";
    break;
  case POST:
    id = "post-f";
    break;
  }

  auto f_it = id_map.find(id);

  if(f_it == id_map.end())
    throw error() << "undeclared function `" << id << '\'';

  const auto &f = f_it->second;
  DATA_INVARIANT(f.type.id() == ID_mathematical_function,
    "functions must have function type");
  const auto &f_type = to_mathematical_function_type(f.type);

  exprt::operandst arguments;
  arguments.resize(f_type.domain().size());

  assert(f.parameters.size()==f_type.domain().size());

  // get arguments
  for(std::size_t i = 0; i < f_type.domain().size(); i++)
  {
    std::string var_id = id2string(f.parameters[i]) + suffix;

    if(id_map.find(var_id) == id_map.end())
      throw error() << "use of undeclared variable `" << var_id << '\'';

    arguments[i] = symbol_exprt(var_id, f_type.domain()[i]);
  }

  return function_application_exprt(
    symbol_exprt(id, f.type),
    arguments);
}

void sygus_parsert::generate_invariant_constraints()
{
  // pre-condition application
  function_application_exprt pre_f =
    apply_function_to_variables(PRE, UNPRIMED);

  // invariant application
  function_application_exprt inv =
    apply_function_to_variables(INV, UNPRIMED);

  function_application_exprt primed_inv =
    apply_function_to_variables(INV, PRIMED);

  // transition function application
  function_application_exprt trans_f =
    apply_function_to_variables(TRANS, UNPRIMED);

  //post-condition function application
  function_application_exprt post_f =
    apply_function_to_variables(POST, UNPRIMED);

  // create constraints
  implies_exprt pre_condition(pre_f, inv);
  constraints.push_back(pre_condition);

  and_exprt inv_and_transition(inv, trans_f);
  implies_exprt transition_condition(inv_and_transition, primed_inv);
  constraints.push_back(transition_condition);

  implies_exprt post_condition(inv, post_f);
  constraints.push_back(post_condition);
}

void sygus_parsert::NTDef_seq()
{
  // it is not necessary to give a syntactic template
  uint8_t openCount = 0u;
  while(smt2_tokenizer.peek()!=smt2_tokenizert::CLOSE || openCount)
  {
    switch(smt2_tokenizer.next_token())
    {
      case smt2_tokenizert::OPEN:
      ++openCount;
      break;
      case smt2_tokenizert::CLOSE:
      --openCount;
      break;
      case smt2_tokenizert::END_OF_FILE:
      case smt2_tokenizert::KEYWORD:
      case smt2_tokenizert::NONE:
      case smt2_tokenizert::NUMERAL:
      case smt2_tokenizert::STRING_LITERAL:
      case smt2_tokenizert::SYMBOL:
      // Ignore grammar.
      break;
    }
  }
}

void sygus_parsert::GTerm_seq()
{
  while(smt2_tokenizer.peek()!=smt2_tokenizert::CLOSE)
  {
    GTerm();
  }
}

void sygus_parsert::NTDef()
{
  // (Symbol Sort GTerm+)
  if(smt2_tokenizer.next_token()!=smt2_tokenizert::OPEN)
    throw error("NTDef must begin with '('");

  if(smt2_tokenizer.peek()==smt2_tokenizert::OPEN)
    smt2_tokenizer.next_token(); // symbol might be in another set of parenthesis

  if(smt2_tokenizer.next_token()!=smt2_tokenizert::SYMBOL)
    throw error("NTDef must have a symbol");

  sort();

  GTerm_seq();

  if(smt2_tokenizer.next_token()!=smt2_tokenizert::CLOSE)
    throw error("NTDef must end with ')'");
}

void sygus_parsert::GTerm()
{
  // production rule

  switch(smt2_tokenizer.next_token())
  {
  case smt2_tokenizert::SYMBOL:
  case smt2_tokenizert::NUMERAL:
  case smt2_tokenizert::STRING_LITERAL:
    break;

  case smt2_tokenizert::OPEN:
    while(smt2_tokenizer.peek()!=smt2_tokenizert::CLOSE)
    {
      GTerm();
    }

    smt2_tokenizer.next_token(); // eat ')'
    break;

  case smt2_tokenizert::NONE:
  case smt2_tokenizert::END_OF_FILE:
  case smt2_tokenizert::KEYWORD:
  case smt2_tokenizert::CLOSE:
    throw error("Unexpected GTerm");
  }
}

void sygus_parsert::expand_function_applications(exprt &expr)
{
  for(exprt &op : expr.operands())
    expand_function_applications(op);

  if(expr.id()==ID_function_application)
  {
    auto &app=to_function_application_expr(expr);

    // look it up
    DATA_INVARIANT(app.function().id()==ID_symbol, "function must be symbol");
    irep_idt identifier=to_symbol_expr(app.function()).get_identifier();
    auto f_it=id_map.find(identifier);

    if(f_it!=id_map.end())
    {
      const auto &f=f_it->second;

      if(synth_fun_set.find(to_symbol_expr(app.function()))!=synth_fun_set.end())
      {
        to_symbol_expr(app.function()).set_identifier("synth_fun::"+id2string(identifier));
        return; // do not expand
      }

      for(const auto &arg: app.arguments())
      {
        if(arg.type().id()==ID_mathematical_function)
        {
          return; // do not expand
        }
      }

      DATA_INVARIANT(f.type.id() == ID_mathematical_function,
        "functions must have function type");
      const auto &f_type = to_mathematical_function_type(f.type);

      for(const auto &d: f_type.domain())
      {
        if(d.id()==ID_mathematical_function)
        {
          return; // do not expand
        }
      }

      assert(f_type.domain().size()==
             app.arguments().size());

      replace_symbolt replace_symbol;

      std::map<irep_idt, exprt> parameter_map;
      for(std::size_t i=0; i<f_type.domain().size(); i++)
      {
        const auto &parameter_type = f_type.domain()[i];
        const auto &parameter_id = f.parameters[i];

        replace_symbol.insert(
          symbol_exprt(parameter_id, parameter_type),
          app.arguments()[i]);
      }

      exprt body=f.definition;
      replace_symbol(body);
      expand_function_applications(body);
      expr=body;
    }
  }
  else if(expr.id()==ID_symbol)
  {
    // deal with defined symbols
    // look it up
    irep_idt identifier=to_symbol_expr(expr).get_identifier();
    auto f_it=id_map.find(identifier);

    if(f_it!=id_map.end())
    {
      if(synth_fun_set.find(to_symbol_expr(expr))!=synth_fun_set.end())
        return; // do not expand

      const auto &f=f_it->second;

      if(f.definition.is_not_nil() &&
         f.type.id() != ID_mathematical_function)
      {
        expr = f.definition;
        // recursively!
        expand_function_applications(expr);
      }
    }
  }
}