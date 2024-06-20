#pragma once

#include "viras/output.h"
#include "viras/predicate.h"
#include "viras/derive.h"

namespace viras {


  template<class C, class T>
  struct WithConfig { 
    C* config; 
    T inner; 

    friend bool operator!=(WithConfig l, WithConfig r) 
    { return !(l == r); }

    friend std::ostream& operator<<(std::ostream& out, WithConfig const& self)
    { return out << output::ptr(self.inner); }

    DERIVE_TUPLE(WithConfig, inner)
    DERIVE_TUPLE_EQ
    DERIVE_TUPLE_LESS
  };

  template<class C> struct Term    : public WithConfig<C, typename C::Term   > {};
  template<class C> struct Numeral : public WithConfig<C, typename C::Numeral> {};
  template<class C> struct Var     : public WithConfig<C, typename C::Var    > {};
  template<class C> struct Literal : public WithConfig<C, typename C::Literal> {
    Term<C> term() const
    { return Term<C> {this->config, this->config->term_of_literal(this->inner)}; }

    PredSymbol symbol() const
    { return this->config->symbol_of_literal(this->inner); }

    friend std::ostream& operator<<(std::ostream& out, Literal<C> const& self)
    { return out << self.term() << " " << self.symbol() << " 0"; }
  };
  template<class C>
  struct Literals : public WithConfig<C, typename C::Literals> {
    auto size() const { return this->config->literals_size(this->inner); }
    auto operator[](size_t idx) const { 
      return Literal<C> { this->config, this->config->literals_get(this->inner, idx) }; 
    }
  };

  template<class C>
  Term<C> to_term(Var<C> n) 
  { return Term<C> { n.config, n.config->term(n.inner), }; }

  template<class C>
  Term<C> to_term(Numeral<C> n) 
  { return Term<C> { n.config, n.config->term(n.inner), }; }

  template<class C>
  Numeral<C> to_numeral(C* c, int n) 
  { return Numeral<C> { c, c->numeral(n), }; }

  template<class C>
  Term<C> to_term(C* c, int n) 
  { return to_term(to_numeral(c,n)); }


  namespace sugar {


    ///////////////////////////////////////
    // PRIMARY OPERATORS
    ///////////////////////////////////////

    template<class C>
    Term<C> operator+(Term<C> lhs, Term<C> rhs) 
    {
      VIRAS_ASSERT(lhs.config == rhs.config);
      return Term<C> {lhs.config, lhs.config->add(lhs.inner, rhs.inner)};
    }

    template<class C>
    Numeral<C> operator+(Numeral<C> lhs, Numeral<C> rhs) 
    { 
      VIRAS_ASSERT(lhs.config == rhs.config);
      return Numeral<C> { lhs.config, lhs.config->add(lhs.inner, rhs.inner)}; 
    }

    template<class C>
    Term<C> operator*(Numeral<C> lhs, Term<C> rhs) 
    {
      VIRAS_ASSERT(lhs.config == rhs.config);
      return Term<C> {lhs.config, lhs.config->mul(lhs.inner, rhs.inner)};
    }

    template<class C>
    Numeral<C> operator*(Numeral<C> lhs, Numeral<C> rhs) 
    {
      VIRAS_ASSERT(lhs.config == rhs.config);
      return Numeral<C> {lhs.config, lhs.config->mul(lhs.inner, rhs.inner)};
    }

    template<class C>
    bool operator<=(Numeral<C> const& lhs, Numeral<C> const& rhs) 
    { return lhs.config->leq(lhs.inner, rhs.inner); }

    template<class C>
    bool operator<(Numeral<C> const& lhs, Numeral<C> const& rhs) 
    { return lhs.config->less(lhs.inner, rhs.inner); }

    ///////////////////////////////////////
    // INTERDEFINED OPERATORS
    ///////////////////////////////////////

#define __VIRAS__DEF_MINUS(CType)                                                                  \
    template<class C>                                                                     \
    CType operator-(CType const& x)                                                       \
    { return to_numeral(x.config, -1) * x; }                                              \
                                                                                          \
    template<class C>                                                                     \
    auto operator-(CType const& x, CType const& y)                                        \
    { return x + -y; }                                                                    \

    __VIRAS__DEF_MINUS(Numeral<C>)
    __VIRAS__DEF_MINUS(Term<C>)

    template<class C>
    bool operator>=(Numeral<C> const& lhs, Numeral<C> const& rhs) 
    { return rhs <= lhs; }

    template<class C>
    bool operator>(Numeral<C> const& lhs, Numeral<C> const& rhs) 
    { return rhs < lhs; }


    ///////////////////////////////////////
    // LIFTED OPERATORS
    ///////////////////////////////////////

#define __VIRAS__LIFT_NUMERAL_TO_TERM_L(fn)                                                        \
    template<class C>                                                                     \
    auto fn(Numeral<C> const& lhs, Term<C> const& rhs)                                    \
    { return fn(to_term(lhs), rhs); }

#define __VIRAS__LIFT_NUMERAL_TO_TERM_R(fn)                                                        \
    template<class C>                                                                     \
    auto fn(Term<C> const& lhs, Numeral<C> const& rhs)                                    \
    { return fn(lhs, to_term(rhs)); }

#define __VIRAS__LIFT_NUMERAL_TO_TERM(fn)                                                          \
    __VIRAS__LIFT_NUMERAL_TO_TERM_L(fn)                                                            \
    __VIRAS__LIFT_NUMERAL_TO_TERM_R(fn)                                                            \

    __VIRAS__LIFT_NUMERAL_TO_TERM(operator+)
    __VIRAS__LIFT_NUMERAL_TO_TERM(operator-)

#define __VIRAS__LIFT_INT_TO_NUMERAL(function, CType)                                              \
    __VIRAS__LIFT_INT_TO_NUMERAL_L(function, CType)                                                \
    __VIRAS__LIFT_INT_TO_NUMERAL_R(function, CType)                                                \


#define __VIRAS__LIFT_INT_TO_NUMERAL_L(function, CType)                                            \
    template<class C>                                                                     \
    auto function(int lhs, CType rhs)                                                     \
    { return function(Numeral<C> {rhs.config, rhs.config->numeral(lhs)}, rhs); }          \

#define __VIRAS__LIFT_INT_TO_NUMERAL_R(function, CType)                                            \
    template<class C>                                                                     \
    auto function(CType lhs, int rhs)                                                     \
    { return function(lhs, Numeral<C> {lhs.config, lhs.config->numeral(rhs)}); }          \

#define __VIRAS__LIFT_INT_TO_NUMERAL(function, CType)                                              \
    __VIRAS__LIFT_INT_TO_NUMERAL_L(function, CType)                                                \
    __VIRAS__LIFT_INT_TO_NUMERAL_R(function, CType)                                                \

    __VIRAS__LIFT_INT_TO_NUMERAL(operator+, Numeral<C>)
    __VIRAS__LIFT_INT_TO_NUMERAL(operator-, Numeral<C>)
    __VIRAS__LIFT_INT_TO_NUMERAL(operator*, Numeral<C>)

    __VIRAS__LIFT_INT_TO_NUMERAL(operator==, Numeral<C>)
    __VIRAS__LIFT_INT_TO_NUMERAL(operator!=, Numeral<C>)
    __VIRAS__LIFT_INT_TO_NUMERAL(operator<=, Numeral<C>)
    __VIRAS__LIFT_INT_TO_NUMERAL(operator>=, Numeral<C>)
    __VIRAS__LIFT_INT_TO_NUMERAL(operator< , Numeral<C>)
    __VIRAS__LIFT_INT_TO_NUMERAL(operator> , Numeral<C>)

    __VIRAS__LIFT_INT_TO_NUMERAL(operator+, Term<C>)
    __VIRAS__LIFT_INT_TO_NUMERAL(operator-, Term<C>)
    __VIRAS__LIFT_INT_TO_NUMERAL_L(operator*, Term<C>)


     // MULTIPLICATION
     // DIVISION

    template<class C>
    Numeral<C> operator/(Numeral<C> lhs, Numeral<C> rhs) 
    { return Numeral<C>{ rhs.config, rhs.config->inverse(rhs.inner) } * lhs; }

    __VIRAS__LIFT_INT_TO_NUMERAL(operator/, Numeral<C>)

    template<class C>
    Term<C> operator/(Term<C> lhs, Numeral<C> rhs) 
    { return (1 / rhs) * lhs; }

    __VIRAS__LIFT_INT_TO_NUMERAL_R(operator/, Term<C>)

#define __VIRAS__LITERAL_CONSTRUCTION_OPERATOR(fn, Sym)                                            \
    template<class C>                                                                     \
    Literal<C> fn(Term<C> lhs, Term<C> rhs)                                               \
    {                                                                                     \
      VIRAS_ASSERT(lhs.config == rhs.config);                                             \
      return Literal<C> { lhs.config, lhs.config->create_literal((lhs - rhs).inner, Sym) }; \
    }                                                                                     \
                                                                                          \
    __VIRAS__LIFT_NUMERAL_TO_TERM(fn)                                                              \
    __VIRAS__LIFT_INT_TO_NUMERAL(fn, Term<C>)                                                      \

    __VIRAS__LITERAL_CONSTRUCTION_OPERATOR(operator> , PredSymbol::Gt);
    __VIRAS__LITERAL_CONSTRUCTION_OPERATOR(operator>=, PredSymbol::Geq);
    __VIRAS__LITERAL_CONSTRUCTION_OPERATOR(eq, PredSymbol::Neq);
    __VIRAS__LITERAL_CONSTRUCTION_OPERATOR(neq, PredSymbol::Eq);

  } // namespace sugar

#undef __VIRAS__DEF_MINUS
#undef __VIRAS__LIFT_NUMERAL_TO_TERM_L
#undef __VIRAS__LIFT_NUMERAL_TO_TERM_R
#undef __VIRAS__LIFT_NUMERAL_TO_TERM
#undef __VIRAS__LIFT_INT_TO_NUMERAL
#undef __VIRAS__LIFT_INT_TO_NUMERAL_L
#undef __VIRAS__LIFT_INT_TO_NUMERAL_R
#undef __VIRAS__LIFT_INT_TO_NUMERAL
#undef __VIRAS__LITERAL_CONSTRUCTION_OPERATOR

  using namespace sugar;

  template<class C>
  Numeral<C> abs(Numeral<C> x) 
  { return x < 0 ? -x : x; }

  template<class C>
  Numeral<C> num(Numeral<C> x)
  { return Numeral<C> { x.config, x.config->num(x.inner) }; }

  template<class C>
  Numeral<C> den(Numeral<C> x) 
  { return Numeral<C> { x.config, x.config->den(x.inner) }; }

  template<class C>
  Numeral<C> lcm(Numeral<C> l, Numeral<C> r)
  { 
    auto cn = [&](auto x) { return Numeral<C> { l.config, x }; };
    return cn(l.config->lcm(num(l).inner, num(r).inner)) 
         / cn(l.config->gcd(den(l).inner, den(r).inner));  
  }

   // floor
  template<class C>
  Term<C> floor(Term<C> x) 
  { return Term<C> { x.config, x.config->floor(x.inner), }; }

  template<class C>
  Term<C> ceil(Term<C> x) 
  { return -floor(-x); }


  template<class C>
  Numeral<C> floor(Numeral<C> x) 
  { return Numeral<C> { x.config, x.config->floor(x.inner), }; }


  template<class C>
  Term<C> quot(Term<C> t, Numeral<C> p) { return floor(t / p); }

  template<class C>
  Term<C> rem(Term<C> t, Numeral<C> p) { return t - p * quot(t, p); }

  template<class C, class IfVar, class IfOne, class IfMul, class IfAdd, class IfFloor>
  auto matchTerm(Term<C> t, 
      IfVar   if_var, 
      IfOne   if_one, 
      IfMul   if_mul, 
      IfAdd   if_add, 
      IfFloor if_floor
      ) -> decltype(auto) {
    return t.config->matchTerm(t.inner,
      [&](auto x) { return if_var(Var<C> { t.config, x }); }, 
      [&]() { return if_one(); }, 
      [&](auto l, auto r) { return if_mul(Numeral<C> {t.config, l},Term<C>{t.config, r}); }, 
      [&](auto l, auto r) { return if_add(Term<C>{t.config, l},Term<C>{t.config, r}); }, 
      [&](auto x) { return if_floor(Term<C>{t.config, x}); }
         );
  }


  template<class C>
  Term<C> subs(Term<C> self, Var<C> var, Term<C> by) {
    using namespace sugar;
    return matchTerm(self, 
      /* var y */     [&](auto v)         { return v == var ? by : self; }, 
      /* numeral 1 */ [&]()               { return self; }, 
      /* k * t */     [&](auto k, auto t) { return k * subs(t, var, by); }, 
      /* l + r */     [&](auto l, auto r) { return subs(l,var,by) + subs(r,var,by); }, 
      /* floor */     [&](auto t)         { return floor(subs(t,var,by)); });
  }


} // namespace viras
