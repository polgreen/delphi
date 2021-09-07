#ifndef CPROVER_FASTSYNTH_SYNTH_ENCODING_H_
#define CPROVER_FASTSYNTH_SYNTH_ENCODING_H_

#include "../problem.h"

#include <util/mathematical_expr.h>
#include <solvers/decision_procedure.h>

#include <set>

struct e_datat
{
public:
  e_datat():enable_bitwise(false), enable_division(false), setup_done(false) { }

  exprt operator()(
    const function_application_exprt &expr,
    const std::size_t program_size,
    bool enable_bitwise,
    bool enable_division)
  {
    setup(expr, program_size, enable_bitwise);
    return result(expr.arguments());
  }

  struct instructiont
  {
    explicit instructiont(std::size_t _pc):pc(_pc)
    {
    }

    std::size_t pc;

    // constant, always the last resort
    symbol_exprt constant_val = symbol_exprt::typeless(ID_empty_string);

    struct optiont
    {
      optiont():parameter_number(0), kind(NONE),
        operand0(0), operand1(0), operand2(0)
      {
      }

      symbol_exprt sel = symbol_exprt::typeless(ID_empty_string);
      irep_idt operation;
      std::size_t parameter_number;
      enum { NONE, PARAMETER, UNARY, BINARY, BINARY_PREDICATE, ITE } kind;
      std::size_t operand0, operand1, operand2;
      exprt type;
    };

    using optionst=std::vector<optiont>;
    optionst options;

    optiont &add_option(const irep_idt &sel_identifier)
    {
      options.push_back(optiont());
      options.back().sel=symbol_exprt(sel_identifier, bool_typet());
      return options.back();
    }

    // generate a constraint for the instruction
    // - for a given word type
    // - for a set of arguments
    // - for a given vector of previous results
    exprt constraint(
      const typet &word_type,
      const std::vector<exprt> &arguments,
      const std::vector<exprt> &results);

  protected:
    if_exprt chain(
      const symbol_exprt &selector,
      const exprt &,
      const exprt &);
  };

  std::vector<instructiont> instructions;

  // result of the function application
  // for a set of arguments

  symbol_exprt function_symbol = symbol_exprt::typeless(ID_empty_string);
  std::vector<symbol_exprt> parameters;
  typet return_type;
  typet word_type;

  exprt get_function(const decision_proceduret &,
                     bool symbolic_constants) const;

  using constraintst=std::list<exprt>;
  constraintst constraints;

  typet compute_word_type();

  using instancest=
    std::map<function_application_exprt::argumentst, std::size_t>;
  instancest instances;

  using argumentst=
    function_application_exprt::argumentst;

  std::size_t instance_number(const argumentst &);

  bool enable_bitwise;
  bool enable_division;

  /// Pre-configured constants to include in the expression set.
  std::set<constant_exprt> literals;

protected:
  bool setup_done;

  exprt result(const argumentst &);

  void setup(
    const function_application_exprt &,
    const std::size_t program_size,
    const bool enable_bitwise);
};

class synth_encodingt
{
public:
  synth_encodingt():program_size(1), enable_bitwise(false), enable_division(false)
  {
  }

  exprt operator()(const exprt &);

  solutiont get_solution(const decision_proceduret &) const;

  std::string suffix;
  std::size_t program_size;
  bool enable_bitwise;
  bool enable_division;
  std::map<irep_idt, synth_functiont> synth_funs;

  using constraintst=std::list<exprt>;
  constraintst constraints;

  /// Pre-configured constants to include in the expression set.
  std::set<constant_exprt> literals;

  void clear();

protected:
  std::map<symbol_exprt, e_datat> e_data_map;
};

#endif /* CPROVER_FASTSYNTH_SYNTH_ENCODING_H_ */