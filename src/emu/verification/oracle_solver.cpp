#include "oracle_solver.h"

#include "oracle_response_parser.h"

#include <util/expr.h>
#include <util/format_expr.h>
#include <util/run.h>
#include <util/std_expr.h>
#include <util/string_utils.h>

#include <sstream>

oracle_solvert::oracle_solvert(
  decision_proceduret &__sub_solver,
  const std::vector<oracle_constraint_gent> &__oracles,
  message_handlert &__message_handler) :
  sub_solver(__sub_solver),
  oracles(__oracles),
  log(__message_handler)
{
}

void oracle_solvert::set_to(const exprt &expr, bool value)
{
  sub_solver.set_to(expr, value);
}

exprt oracle_solvert::handle(const exprt &expr)
{
  return sub_solver.handle(expr);
}

exprt oracle_solvert::get(const exprt &expr) const
{
  return sub_solver.get(expr);
}

void oracle_solvert::print_assignment(std::ostream &out) const
{
  sub_solver.print_assignment(out);
}

std::string oracle_solvert::decision_procedure_text() const
{
  return "oracles + " + sub_solver.decision_procedure_text();
}

oracle_solvert::check_resultt oracle_solvert::check_oracles()
{
  oracle_solvert::check_resultt result = CONSISTENT;

  for(std::size_t oracle_index = 0; oracle_index < oracles.size(); oracle_index++)
  {
    switch(check_oracle(oracle_index))
    {
    case INCONSISTENT:
      result = INCONSISTENT;
      break;

    case CONSISTENT:
      break;

    case ERROR:
      return ERROR; // abort
    }
  }

  return result;
}

oracle_solvert::check_resultt oracle_solvert::check_oracle(std::size_t oracle_index)
{
  const oracle_constraint_gent &oracle = oracles[oracle_index];

  // evaluate the input vector
  std::vector<exprt> inputs;
  inputs.reserve(oracle.input_parameters.size());

  for(std::size_t input_index = 0; input_index < oracle.input_parameters.size(); input_index++)
  {
    const auto &input = oracle.input_parameters[input_index];
    std::string identifier = "oracle_"+std::to_string(oracle_index)+"_input_"+std::to_string(input_index);
    inputs.push_back(get(symbol_exprt(identifier, input.type())));
  }

  std::vector<std::string> argv;
  argv.push_back(id2string(oracle.binary_name));

  for(auto &input : inputs)
  {
    std::ostringstream stream;
    stream << format(input);
    argv.push_back(stream.str());
  }

  log.status() << "Running oracle";
  for(auto &arg : argv)
    log.status() << ' ' << arg;
  log.status() << messaget::eom;

  // run the oracle binary
  std::ostringstream stdout_stream;
  
  auto run_result = run(
    id2string(oracle.binary_name),
    argv,
    "",
    stdout_stream,
    "");

  if(run_result != 0)
  {
    log.error() << "oracle " << oracle.binary_name << " has failed" << messaget::eom;
    return ERROR;
  }

  // we assume that the oracle returns the result in SMT-LIB format
  std::istringstream oracle_response_istream(stdout_stream.str());
  auto response = oracle_response_parser(oracle_response_istream);

  (void)response;

#if 0
  // parse these lines into expressions
  std::vector<exprt> return_values;
  return_values.reserve(lines.size());

  for(auto &line : lines)
    return_values.push_back(parse(line));

  if(oracle.return_parameters.size() != return_values.size())
  {
    log.error() << "oracle " << oracle.binary_name << " has returned "
                << return_values.size() << " values, but " << oracle.return_parameters.size()
                << " are expected" << messaget::eom;
    return ERROR;
  }
#endif

  // check whether the constraint is satisfied

  return CONSISTENT;
}

exprt oracle_solvert::parse(const std::string &text) const
{
  return true_exprt();
}

void oracle_solvert::setup_oracle_equalities()
{
  for(std::size_t oracle_index = 0; oracle_index < oracles.size(); oracle_index++)
  {
    auto &oracle = oracles[oracle_index];

    for(std::size_t input_index = 0; input_index < oracle.input_parameters.size(); input_index++)
    {
      const auto &input = oracle.input_parameters[input_index];
      std::string identifier = "oracle_"+std::to_string(oracle_index)+"_input_"+std::to_string(input_index);
      set_to_true(equal_exprt(symbol_exprt(identifier, input.type()), input));
    }

    for(std::size_t return_index = 0; return_index < oracle.return_parameters.size(); return_index++)
    {
      const auto &output = oracle.return_parameters[return_index];
      std::string identifier = "oracle_"+std::to_string(oracle_index)+"_return_"+std::to_string(return_index);
      set_to_true(equal_exprt(symbol_exprt(identifier, output.type()), output));
    }

    std::string identifier = "oracle_"+std::to_string(oracle_index)+"_constraint";
    set_to_true(equal_exprt(symbol_exprt(identifier, oracle.constraint.type()), oracle.constraint));
  }
}

decision_proceduret::resultt oracle_solvert::dec_solve()
{
  number_of_solver_calls++;

  setup_oracle_equalities();

  while(true)
  {
    switch(sub_solver())
    {
    case resultt::D_SATISFIABLE:
      switch(check_oracles())
      {
      case INCONSISTENT:
        break; // constraint added, we'll do another iteration

      case CONSISTENT:
        return resultt::D_SATISFIABLE;

      case ERROR:
        return resultt::D_ERROR;
      }

    case resultt::D_UNSATISFIABLE:
      return resultt::D_UNSATISFIABLE;

    case resultt::D_ERROR:
      return resultt::D_ERROR;
    }
  }
}
