#include "sygus_parser.h"
#include "expr2sygus.h"

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
      add_unique_id(id, exprt(ID_nil, param_sort));

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

    auto signature= function_signature_definition();

    // we'll tweak the type in case there are no parameters
    if(signature.type.id() != ID_mathematical_function)
    {
      // turn into () -> signature.type
      signature.type = mathematical_function_typet({}, signature.type);
    }
    syntactic_templatet grammar = NTDef_seq();

    auto f_it = id_map.emplace(
      std::piecewise_construct,
      std::forward_as_tuple(id),
      std::forward_as_tuple(idt::VARIABLE, nil_exprt()));

    f_it.first->second.type = signature.type;
    f_it.first->second.parameters = signature.parameters;

    synthesis_functions.insert( 
      std::pair<irep_idt, synth_functiont> 
      (id, synth_functiont(grammar, signature.type, signature.parameters)));
    // restore renamings
    std::swap(renaming_map, old_renaming_map);
  };

  commands["synth-inv"] = [this]
  {
    if(smt2_tokenizer.next_token()!=smt2_tokenizert::SYMBOL)
      throw error("expected a symbol after synth-fun");

    // save the renaming map
    renaming_mapt old_renaming_map = renaming_map;
    irep_idt id=smt2_tokenizer.get_buffer();

    if(id_map.find(id)!=id_map.end())
      throw error() << "function `" << id << "' declared twice";

    auto signature=inv_function_signature();

    // we'll tweak the type in case there are no parameters
    if(signature.type.id() != ID_mathematical_function)
    {
      // turn into () -> signature.type
      signature.type = mathematical_function_typet({}, signature.type);
    }
    syntactic_templatet grammar = NTDef_seq();

    auto f_it = id_map.emplace(
      std::piecewise_construct,
      std::forward_as_tuple(id),
      std::forward_as_tuple(idt::VARIABLE, nil_exprt()));

    f_it.first->second.type = signature.type;
    f_it.first->second.parameters = signature.parameters;

    synthesis_functions.insert( 
      std::pair<irep_idt, synth_functiont> 
      (id, synth_functiont(grammar, signature.type, signature.parameters)));
    // restore renamings
    std::swap(renaming_map, old_renaming_map);
  };

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
    irep_idt inv,pre,trans,post;
    if(next_token() != smt2_tokenizert::SYMBOL)
      throw error() << "expected a symbol for invariant in inv-constraint" ;
    inv = smt2_tokenizer.get_buffer();
    if(next_token() != smt2_tokenizert::SYMBOL)
      throw error() << "expected a symbol for pre in inv-constraint" ;
    pre=smt2_tokenizer.get_buffer();
    if(next_token() != smt2_tokenizert::SYMBOL)
      throw error() << "expected a symbol for trans in inv-constraint" ;
    trans=smt2_tokenizer.get_buffer();
    if(next_token() != smt2_tokenizert::SYMBOL)
      throw error() << "expected a symbol for post in inv-constraint" ;
    post=smt2_tokenizer.get_buffer();

    generate_invariant_constraints(inv, pre, trans, post);
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
  irep_idt id,
  invariant_variablet var_use)
{
  std::string suffix;
  if(var_use == PRIMED)
  {
    suffix="!";
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
    std::string var_id = clean_id(f.parameters[i]) + suffix;
    const typet &var_type = f_type.domain()[i];

    if(id_map.find(var_id) == id_map.end())
    {
      // declare variable
      add_unique_id(var_id, exprt(ID_nil, var_type));
      variable_set.insert(symbol_exprt(var_id, var_type));
    }

    arguments[i] = symbol_exprt(var_id, var_type);
  }
  return function_application_exprt(
    symbol_exprt(id, f.type),
    arguments);
}

void sygus_parsert::generate_invariant_constraints(
    const irep_idt &inv, const irep_idt &pre, const irep_idt &trans, const irep_idt &post)

{
  // pre-condition application
  function_application_exprt pre_f =
    apply_function_to_variables(pre, UNPRIMED);

  // invariant application
  function_application_exprt inv_f =
    apply_function_to_variables(inv, UNPRIMED);

  function_application_exprt primed_inv =
    apply_function_to_variables(inv, PRIMED);

  // transition function application
  function_application_exprt trans_f =
    apply_function_to_variables(trans, UNPRIMED);

  //post-condition function application
  function_application_exprt post_f =
    apply_function_to_variables(post, UNPRIMED);

  function_application_exprt primed_post =
    apply_function_to_variables(post, PRIMED);

  // create constraints
  and_exprt inv_p(inv_f, post_f);
  implies_exprt pre_condition(pre_f, inv_p); // init => inv & post
  constraints.push_back(pre_condition);
  and_exprt inv_p_primed(primed_inv, primed_post); 
  and_exprt inv_and_transition(inv_p, trans_f); // (inv & post & trans)
  implies_exprt transition_condition(inv_and_transition, inv_p_primed); //(inv & post & trans) => inv' & post'
  constraints.push_back(transition_condition);

  implies_exprt post_condition(inv_p, post_f); // inv & post => post. Really not needed. 
  constraints.push_back(post_condition);
  synth_fun_helpers.push_back(post_f);

  implies_exprt pre_condition2(pre_f, inv_f);
  alternative_constraints.push_back(pre_condition2);
  and_exprt inv_and_transition2(inv_f, trans_f);
  implies_exprt transition_condition2(inv_and_transition2, primed_inv);
  alternative_constraints.push_back(transition_condition2);

  implies_exprt post_condition2(inv_f, post_f);
  alternative_constraints.push_back(post_condition2);
}

syntactic_templatet sygus_parsert::NTDef_seq()
{
  syntactic_templatet result;
  std::vector<symbol_exprt> non_terminals;

  // it is not necessary to give a syntactic template
  if(smt2_tokenizer.peek()==smt2_tokenizert::CLOSE)
    return result;
  
  if(smt2_tokenizer.next_token()!=smt2_tokenizert::OPEN)
    throw error("Nonterminal list must begin with '('");

  // parse list of nonterminals
  while(smt2_tokenizer.peek()!=smt2_tokenizert::CLOSE)
  {
    auto next_nonterminal = NTDef();
    non_terminals.push_back(next_nonterminal);
    result.nt_ids.push_back(next_nonterminal.get_identifier());
  }
  // eat the close
  smt2_tokenizer.next_token();
  // eat the open
  smt2_tokenizer.next_token();

  for(const auto &nt: non_terminals)
  {
    std::vector<exprt> production_rule = GTerm_seq(nt);
    result.production_rules[nt.get_identifier()] = production_rule;
  }
  smt2_tokenizer.next_token(); // eat the close

  return result;
}

std::vector<exprt> sygus_parsert::GTerm_seq(const symbol_exprt &nonterminal)
{
  irep_idt id;
  std::vector<exprt> rules;

  if(smt2_tokenizer.next_token()!=smt2_tokenizert::OPEN)
    throw error("Grammar production rule must start with '('");

  if(smt2_tokenizer.next_token()!=smt2_tokenizert::SYMBOL)
    throw error("Grammar production rule must start with non terminal name");
  
  id = smt2_tokenizer.get_buffer();
  typet nt_sort = sort(); 
  if(id!=nonterminal.get_identifier() || nt_sort != nonterminal.type())
    throw error("Grouped rule listing does not match the name in order) from the predeclaration");

  if(smt2_tokenizer.next_token()!=smt2_tokenizert::OPEN)
    throw error("Grammar production rule must start with '('");

  while(smt2_tokenizer.peek()!=smt2_tokenizert::CLOSE)
  {
    auto rule = expression();
    if(rule.type()!=nt_sort)
      throw error("rule does not match sort");
    rules.push_back(rule);
  }
  smt2_tokenizer.next_token(); // eat the close
  if(smt2_tokenizer.next_token()!=smt2_tokenizert::CLOSE)
    throw error("Grammar production rule must end with ')'");

  return rules;
}

symbol_exprt sygus_parsert::NTDef()
{
  // (Symbol Sort)
  if(smt2_tokenizer.next_token()!=smt2_tokenizert::OPEN)
    throw error("NTDef must begin with '('");

  if(smt2_tokenizer.peek()==smt2_tokenizert::OPEN)
    smt2_tokenizer.next_token(); // symbol might be in another set of parenthesis

  if(smt2_tokenizer.next_token()!=smt2_tokenizert::SYMBOL)
    throw error("NTDef must have a symbol");

  irep_idt id = smt2_tokenizer.get_buffer();  
  typet nt_sort = sort();
  add_unique_id(id, exprt(ID_nil, nt_sort));

  if(smt2_tokenizer.next_token()!=smt2_tokenizert::CLOSE)
    throw error("NTDef must end with ')'");
  
  return symbol_exprt(id, nt_sort);
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

      if(synthesis_functions.find(identifier)!=synthesis_functions.end())
      {
        return; // do not expand
      }
      if(oracle_symbols.find(identifier)!=oracle_symbols.end())
        return; //do not expand

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

      // std::map<irep_idt, exprt> parameter_map;
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
      if(synthesis_functions.find(identifier)!=synthesis_functions.end())
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