#pragma once
#include <utility>
#include "viras/iter.h"
#include "viras/predicate.h"
#include "viras/virtual_term.h"

namespace viras {
namespace term_engine {

  namespace ast {

    ///////////////////////////////////////
    // ATOMS
    ///////////////////////////////////////

    static constexpr Infty infty {};
    // struct Infty { bool positive; };
    // inline Infty operator-(Infty const& inf) { return { !inf.positive }; }

    struct Numeral { size_t n; };
    inline Numeral numeral(size_t n)  { return Numeral { n }; };
    inline Numeral operator""_n(unsigned long long n) { return numeral(n); }

    struct TestVar { const char* name; };
    inline TestVar test_var(const char* name)  { return TestVar { name }; };
    inline TestVar operator""_v(const char* name, size_t len) { return test_var(name); }

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
    PRIMARY_OPERATOR(Lcm , lcm       );

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
    UNARY_OPERATOR(Numerator  , numerator  )
    UNARY_OPERATOR(Denominator, denominator)

     template<class T, class V, class O, class M, class A, class F>
     struct Match {
       T t;
       V var; 
       O one; 
       M mul; 
       A add; 
       F floor;
     };

     template<class T, class V, class O, class M, class A, class F>
     Match<T, V, O, M, A, F> match(
       T t,
       V var, 
       O one, 
       M mul, 
       A add, 
       F floor) {
       return Match<T, V, O, M, A, F>{ 
         std::move(t),
         std::move(var),
         std::move(one),
         std::move(mul),
         std::move(add),
         std::move(floor),
       };
     }

    ///////////////////////////////////////
    // INTERDEFINED 
    ///////////////////////////////////////


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

    template<class E>
    auto ceil(E e) { return -floor(-std::move(e)); }

    template<class L, class R>
    auto quot(L l, R r) { return floor(std::move(l) / std::move(r)); }

    template<class T, class P>
    auto rem(T t, P p) { return t - p * quot(t, p); }

  } // namespace ast

    ///////////////////////////////////////
    // EVALUATION 
    ///////////////////////////////////////
  template<class C>
  struct OtherEvaluator 
  {
    C* config;
    using Term    = typename C::Term;
    using Numeral = typename C::Numeral;
    using Var     = typename C::Var;
    using Literal = typename C::Literal;

    // TODO use move instead of copy
    Numeral eval_numeral(Numeral const& n) 
    { return n; }

    Numeral eval_numeral(int const& expr) 
    { return config->numeral(expr); }

    Numeral eval_numeral(ast::Numeral n) 
    { return config->numeral(n.n); }

    template<class L, class R>
    Numeral eval_numeral(ast::Add<L, R> const& expr) 
    { return config->add(eval_numeral(expr.lhs), eval_numeral(expr.rhs)); }

    template<class L, class R>
    Numeral eval_numeral(ast::Mul<L, R> const& expr) 
    { return config->mul(eval_numeral(expr.lhs), eval_numeral(expr.rhs)); }

    template<class L, class R>
    Numeral eval_numeral(ast::Lcm<L, R> const& expr) 
    { 
      using namespace ast;
      return eval_numeral(
            config->lcm(eval_numeral(  numerator(expr.lhs)), eval_numeral(  numerator(expr.rhs))) 
          / config->gcd(eval_numeral(denominator(expr.lhs)), eval_numeral(denominator(expr.rhs))) 
          );
    }

    template<class E>
    Numeral eval_numeral(ast::Numerator<E> const& expr) 
    { return config->num(eval_numeral(expr.inner)); }

    template<class E>
    Numeral eval_numeral(ast::Denominator<E> const& expr) 
    { return config->den(eval_numeral(expr.inner)); }

    template<class E>
    Numeral eval_numeral(ast::Inverse<E> const& expr) 
    { return config->inverse(eval_numeral(expr.inner)); }

    template<class E>
    Numeral eval_numeral(ast::Floor<E> const& expr) 
    { return config->floor(eval_numeral(expr.inner)); }

    template<class E>
    Numeral eval_numeral(ast::Abs<E> const& expr) 
    { 
      using namespace ast;
      return eval_bool(expr >= 0) 
            ? eval_numeral(expr)
            : eval_numeral(-expr); }

    // Term eval_term(int const& expr) 
    // { return config->term(eval_numeral(expr)); }

    Term eval_term(Var const& term) 
    { return config->term(term); }

    Term eval_term(Term const& term) 
    { return term; }

    // Term eval_term(Numeral const& n) 
    // { return config->term(eval_numeral(n)); }

    Term eval_term(ast::Numeral const& n) 
    { return config->term(eval_numeral(n)); }

    template<class L, class R>
    Term eval_term(ast::Add<L, R> const& expr) 
    { return config->add(eval_term(expr.lhs), eval_term(expr.rhs)); }

    template<class L, class R>
    Term eval_term(ast::Mul<L, R> const& expr) 
    { return config->mul(eval_numeral(expr.lhs), eval_term(expr.rhs)); }

    Term eval_term(ast::TestVar expr) 
    { return config->term(config->test_var(expr.name)); }

    template<class E>
    Term eval_term(ast::Floor<E> const& expr) 
    { return config->floor(eval_term(expr.inner)); }


    template<class T>
    Term eval_term(T const& expr) 
    { return config->term(eval_numeral(expr)); }


#define __EVAL_LITERAL(Ast, Sym)                                                          \
    template<class L, class R>                                                            \
    Literal eval_literal(Ast<L, R> expr) {                                    \
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

    VirtualTerm<C> eval_virtual_term(Infty const& expr);
    // { return VirtualTerm<C>({},{},{},{expr}); }

    VirtualTerm<C> eval_virtual_term(Epsilon const& expr);
    // { return VirtualTerm<C>({},{expr},{},{}); }

    VirtualTerm<C> eval_virtual_term(ZComp<C> const& expr);
    // { return VirtualTerm<C>({},{},{expr.period},{}); }

    template<class L, class R>
    VirtualTerm<C> eval_virtual_term(ast::Add<L, R> const& expr);
    // { 
    //   auto lhs = eval_virtual_term(expr.lhs);
    //   auto rhs = eval_virtual_term(expr.rhs);
    //   VIRAS_ASSERT(!bool(lhs.infty  ) || !bool(rhs.infty  ))
    //   VIRAS_ASSERT(!bool(lhs.epsilon) || !bool(rhs.epsilon))
    //   VIRAS_ASSERT(!bool(lhs.period ) || !bool(rhs.period ))
    //   return VirtualTerm<C>(
    //         lhs.term && rhs.term ? std::optional<Term>(*lhs.term  + *rhs.term)
    //       : lhs.term             ? std::optional<Term>(*lhs.term             )
    //       :             rhs.term ? std::optional<Term>(             *rhs.term)
    //       :                        std::optional<Term>(                      ), 
    //       lhs.epsilon ? lhs.epsilon : rhs.epsilon,
    //       lhs.period ? lhs.period : rhs.period,
    //       lhs.infty ? lhs.infty : rhs.infty);
    // }

    template<class T>
    VirtualTerm<C> eval_virtual_term(T const& expr)
    { 
      auto t = eval_term(expr);
      return iter::dummyVal<VirtualTerm<C>>();
      // return VirtualTerm<C>({std::move(t)},{},{},{}); 
    }


  };
  template<class C>
  struct Evaluator 
  {
    C* config;
    using Term    = typename C::Term;
    using Numeral = typename C::Numeral;
    using Var     = typename C::Var;
    using Literal = typename C::Literal;

    // TODO use move instead of copy
    Numeral eval_numeral(Numeral const& n) 
    { return n; }

    Numeral eval_numeral(int const& expr) 
    { return config->numeral(expr); }

    Numeral eval_numeral(ast::Numeral n) 
    { return config->numeral(n.n); }

    template<class L, class R>
    Numeral eval_numeral(ast::Add<L, R> const& expr) 
    { return config->add(eval_numeral(expr.lhs), eval_numeral(expr.rhs)); }

    template<class L, class R>
    Numeral eval_numeral(ast::Mul<L, R> const& expr) 
    { return config->mul(eval_numeral(expr.lhs), eval_numeral(expr.rhs)); }

    template<class L, class R>
    Numeral eval_numeral(ast::Lcm<L, R> const& expr) 
    { 
      using namespace ast;
      return eval_numeral(
            config->lcm(eval_numeral(  numerator(expr.lhs)), eval_numeral(  numerator(expr.rhs))) 
          / config->gcd(eval_numeral(denominator(expr.lhs)), eval_numeral(denominator(expr.rhs))) 
          );
    }

    template<class E>
    Numeral eval_numeral(ast::Numerator<E> const& expr) 
    { return config->num(eval_numeral(expr.inner)); }

    template<class E>
    Numeral eval_numeral(ast::Denominator<E> const& expr) 
    { return config->den(eval_numeral(expr.inner)); }

    template<class E>
    Numeral eval_numeral(ast::Inverse<E> const& expr) 
    { return config->inverse(eval_numeral(expr.inner)); }

    template<class E>
    Numeral eval_numeral(ast::Floor<E> const& expr) 
    { return config->floor(eval_numeral(expr.inner)); }

    template<class E>
    Numeral eval_numeral(ast::Abs<E> const& expr) 
    { 
      using namespace ast;
      return eval_bool(expr >= 0) 
            ? eval_numeral(expr)
            : eval_numeral(-expr); }

    // Term eval_term(int const& expr) 
    // { return config->term(eval_numeral(expr)); }

    Term eval_term(Var const& term) 
    { return config->term(term); }

    Term eval_term(Term const& term) 
    { return term; }

    // Term eval_term(Numeral const& n) 
    // { return config->term(eval_numeral(n)); }

    Term eval_term(ast::Numeral const& n) 
    { return config->term(eval_numeral(n)); }

    template<class L, class R>
    Term eval_term(ast::Add<L, R> const& expr) 
    { return config->add(eval_term(expr.lhs), eval_term(expr.rhs)); }

    template<class L, class R>
    Term eval_term(ast::Mul<L, R> const& expr) 
    { return config->mul(eval_numeral(expr.lhs), eval_term(expr.rhs)); }

    Term eval_term(ast::TestVar expr) 
    { return config->term(config->test_var(expr.name)); }

    template<class E>
    Term eval_term(ast::Floor<E> const& expr) 
    { return config->floor(eval_term(expr.inner)); }


    template<class T>
    Term eval_term(T const& expr) 
    { return config->term(eval_numeral(expr)); }


#define __EVAL_LITERAL(Ast, Sym)                                                          \
    template<class L, class R>                                                            \
    Literal eval_literal(Ast<L, R> expr) {                                    \
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

    VirtualTerm<C> eval_virtual_term(Infty const& expr);
    // { return VirtualTerm<C>({},{},{},{expr}); }

    VirtualTerm<C> eval_virtual_term(Epsilon const& expr);
    // { return VirtualTerm<C>({},{expr},{},{}); }

    VirtualTerm<C> eval_virtual_term(ZComp<C> const& expr);
    // { return VirtualTerm<C>({},{},{expr.period},{}); }

    template<class L, class R>
    VirtualTerm<C> eval_virtual_term(ast::Add<L, R> const& expr);
    // { 
    //   auto lhs = eval_virtual_term(expr.lhs);
    //   auto rhs = eval_virtual_term(expr.rhs);
    //   VIRAS_ASSERT(!bool(lhs.infty  ) || !bool(rhs.infty  ))
    //   VIRAS_ASSERT(!bool(lhs.epsilon) || !bool(rhs.epsilon))
    //   VIRAS_ASSERT(!bool(lhs.period ) || !bool(rhs.period ))
    //   return VirtualTerm<C>(
    //         lhs.term && rhs.term ? std::optional<Term>(*lhs.term  + *rhs.term)
    //       : lhs.term             ? std::optional<Term>(*lhs.term             )
    //       :             rhs.term ? std::optional<Term>(             *rhs.term)
    //       :                        std::optional<Term>(                      ), 
    //       lhs.epsilon ? lhs.epsilon : rhs.epsilon,
    //       lhs.period ? lhs.period : rhs.period,
    //       lhs.infty ? lhs.infty : rhs.infty);
    // }

    template<class T>
    VirtualTerm<C> eval_virtual_term(T const& expr)
    { 
      auto t = eval_term(expr);
      return iter::dummyVal<VirtualTerm<C>>();
      // return VirtualTerm<C>({std::move(t)},{},{},{}); 
    }


  };
  template<class C>
  Evaluator<C> evaluator(C* c) { return Evaluator<C> {c}; }
   

#define viras_eval_literal(config, expr) viras_eval(literal, config, expr)
#define viras_eval_term(config, expr) viras_eval(term, config, expr)
#define viras_eval_numeral(config, expr) viras_eval(numeral, config, expr)
#define viras_eval_bool(config, expr) viras_eval(bool, config, expr)

#define viras_eval(kind, config, expr) [&]() {                                            \
      using namespace viras::term_engine::ast;                                            \
      using viras::term_engine::ast::lcm;                                            \
      return viras::term_engine::evaluator(config).eval_ ## kind(expr);                   \
    }()                                                                                   \


} // term_engine
 
  template<class C>
  Term<C> subs(C* config, Term<C> self, Var<C> var, Term<C> by) {
    return config->matchTerm(self, 
      /* var y */     [&](auto v)         { return v == var ? by : self; }, 
      /* numeral 1 */ [&]()               { return self; }, 
      /* k * t */     [&](auto k, auto t) { return viras_eval_term(config, k * subs(t, var, by)); }, 
      /* l + r */     [&](auto l, auto r) { return viras_eval_term(config, subs(l,var,by) + subs(r,var,by)); }, 
      /* floor */     [&](auto t)         { return viras_eval_term(config, floor(subs(config,t,var,by))); });
  }


} // namespace viras
