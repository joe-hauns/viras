#pragma once
#include <utility>
#include "viras/predicate.h"

namespace viras {
namespace term_engine {


  namespace ast {

  ///////////////////////////////////////
  // ATOMS
  ///////////////////////////////////////

  struct Numeral { size_t n; };
  inline Numeral numeral(size_t n)  { return Numeral { n }; };

  struct TestVar { const char* name; };
  inline TestVar test_var(const char* name)  { return TestVar { name }; };


  ///////////////////////////////////////
  // OPERATORS
  ///////////////////////////////////////

#define PRIMARY_OPERATOR(StructName, operator_fun)                                        \
    template<class L, class R> struct StructName { L lhs; R rhs; };                       \
    template<class L, class R>                                                            \
    StructName<L, R> operator_fun(L l, R r)                                               \
    { return StructName<L,R> { std::move(l), std::move(r)}; }                             \

  PRIMARY_OPERATOR(Add , operator+ );
  PRIMARY_OPERATOR(Mul , operator* );
  PRIMARY_OPERATOR(Less, operator< );
  PRIMARY_OPERATOR(Leq , operator<=);
  PRIMARY_OPERATOR(Eq  , operator==);
  PRIMARY_OPERATOR(Neq , operator!=);

#define UNARY_OPERATOR(StructName, operator_fun)                                          \
    template<class E>                                                                     \
    struct StructName { E inner; };                                                       \
                                                                                          \
    template<class E>                                                                     \
    StructName<E> operator_fun(E e)                                                       \
    { return StructName<E> { std::move(e), }; }                                           \


  UNARY_OPERATOR(Floor  , floor  )
  UNARY_OPERATOR(Inverse, inverse)
  UNARY_OPERATOR(Abs, abs)

  template<class E>
  auto operator-(E e)
  { return -1 * e; }

  template<class L, class R>
  auto operator-(L l, R r)
  { return std::move(l) + (-std::move(r)); }

  template<class L, class R>
  auto operator/(L l, R r)
  { return inverse(std::move(r)) * std::move(l); }

  template<class L, class R>
  auto operator>=(L l, R r) { return std::move(r) <= std::move(l); }

  template<class L, class R>
  auto operator>(L l, R r) { return std::move(r) < std::move(l); }

  inline auto numeral(size_t n, size_t m)  { return numeral(n) / numeral(m); }

  } // namespace ast

  template<class C>
  struct Evaluator {
    C* config;

    // TODO use move instead of copy
    typename C::Numeral eval_numeral(typename C::Numeral const& n) 
    { return n; }

    typename C::Numeral eval_numeral(int const& expr) 
    { return config->numeral(expr); }

    typename C::Numeral eval_numeral(ast::Numeral n) 
    { return config->numeral(n.n); }

    template<class L, class R>
    typename C::Numeral eval_numeral(ast::Add<L, R> const& expr) 
    { return config->add(eval_numeral(expr.lhs), eval_numeral(expr.rhs)); }

    template<class L, class R>
    typename C::Numeral eval_numeral(ast::Mul<L, R> const& expr) 
    { return config->mul(eval_numeral(expr.lhs), eval_numeral(expr.rhs)); }

    template<class E>
    typename C::Numeral eval_numeral(ast::Inverse<E> const& expr) 
    { return config->inverse(eval_numeral(expr.inner)); }

    template<class E>
    typename C::Numeral eval_numeral(ast::Floor<E> const& expr) 
    { return config->floor(eval_numeral(expr.inner)); }


    template<class E>
    typename C::Numeral eval_numeral(ast::Abs<E> const& expr) 
    { 
      using namespace ast;
      return eval_bool(expr >= 0) 
            ? eval_numeral(expr)
            : eval_numeral(-expr); }

    typename C::Term eval_term(int const& expr) 
    { return config->term(eval_numeral(expr)); }

    typename C::Term eval_term(typename C::Var const& term) 
    { return config->term(term); }

    typename C::Term eval_term(typename C::Term const& term) 
    { return term; }

    typename C::Term eval_term(typename C::Numeral const& n) 
    { return config->term(eval_numeral(n)); }

    typename C::Term eval_term(ast::Numeral const& n) 
    { return config->term(eval_numeral(n)); }

    template<class L, class R>
    typename C::Term eval_term(ast::Add<L, R> const& expr) 
    { return config->add(eval_term(expr.lhs), eval_term(expr.rhs)); }

    template<class L, class R>
    typename C::Term eval_term(ast::Mul<L, R> const& expr) 
    { return config->mul(eval_numeral(expr.lhs), eval_term(expr.rhs)); }

    typename C::Term eval_term(ast::TestVar expr) 
    { return config->term(config->test_var(expr.name)); }

    template<class E>
    typename C::Term eval_term(ast::Floor<E> const& expr) 
    { return config->floor(eval_term(expr.inner)); }


#define __EVAL_LITERAL(Ast, Sym)                                                          \
    template<class L, class R>                                                            \
    typename C::Literal eval_literal(Ast<L, R> expr) {                                    \
      using namespace ast;                                                                \
      /* l <= r <-> r - l >= 0 */                                                         \
      return config->create_literal(eval_term(expr.rhs - expr.lhs), Sym);                 \
    }                                                                                     \

    __EVAL_LITERAL(ast::Leq , PredSymbol::Geq)
    __EVAL_LITERAL(ast::Less, PredSymbol::Gt )
    __EVAL_LITERAL(ast::Eq  , PredSymbol::Eq )
    __EVAL_LITERAL(ast::Neq , PredSymbol::Neq)

    template<class L, class R>
    bool eval_bool(ast::Leq<L, R> const& expr) 
    { return config->leq(eval_numeral(expr.lhs), eval_numeral(expr.rhs)); }

    template<class L, class R>
    bool eval_bool(ast::Less<L, R> const& expr) 
    { return config->less(eval_numeral(expr.lhs), eval_numeral(expr.rhs)); }

    template<class L, class R>
    bool eval_bool(ast::Eq<L, R> const& expr) 
    { return config->less(eval_numeral(expr.lhs), eval_numeral(expr.rhs)); }

    template<class L, class R>
    bool eval_bool(ast::Neq<L, R> const& expr) 
    { return config->less(eval_numeral(expr.lhs), eval_numeral(expr.rhs)); }

  };
  template<class C>
  Evaluator<C> evaluator(C* c) { return Evaluator<C> {c}; }
   

#define viras_eval_literal(config, expr) viras_eval(literal, config, expr)
#define viras_eval_term(config, expr) viras_eval(term, config, expr)
#define viras_eval_numeral(config, expr) viras_eval(numeral, config, expr)
#define viras_eval_bool(config, expr) viras_eval(bool, config, expr)

#define viras_eval(kind, config, expr) [&]() {                                            \
      using namespace viras::term_engine::ast;                                            \
      return viras::term_engine::evaluator(config).eval_ ## kind(expr);                   \
    }()                                                                                   \

} // term_engine
} // namespace viras
