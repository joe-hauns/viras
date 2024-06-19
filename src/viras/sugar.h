#pragma once

#include "viras/output.h"
#include "viras/predicate.h"
#include "viras/derive.h"

namespace viras {
namespace sugar {


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

    ///////////////////////////////////////
    // LIFTED OPERATORS
    ///////////////////////////////////////

    template<class C>
    Numeral<C> operator+(Numeral<C> lhs, Numeral<C> rhs) 
    { return Numeral<C> { lhs.config, lhs.config->add(lhs.inner, rhs.inner)}; }

    template<class C>
    Term<C> operator+(Numeral<C> lhs, Term<C> rhs) 
    { return Term<C> { rhs.config, lhs.config->term(lhs.inner)} + rhs; }

    template<class C>
    Term<C> operator+(Term<C> lhs, Numeral<C> rhs) 
    { return lhs + Term<C> { rhs.config, rhs.config->term(rhs.inner), }; }

#define LIFT_INT_TO_NUMERAL(function, CType)                                              \
    LIFT_INT_TO_NUMERAL_L(function, CType)                                                \
    LIFT_INT_TO_NUMERAL_R(function, CType)                                                \


#define LIFT_INT_TO_NUMERAL_L(function, CType)                                            \
    template<class C>                                                                \
    auto function(int lhs, CType rhs)                                                     \
    { return function(Numeral<C> {rhs.config, rhs.config->numeral(lhs)}, rhs); }     \

#define LIFT_INT_TO_NUMERAL_R(function, CType)                                            \
    template<class C>                                                                \
    auto function(CType lhs, int rhs)                                                     \
    { return function(lhs, Numeral<C> {lhs.config, lhs.config->numeral(rhs)}); }     \

#define LIFT_INT_TO_NUMERAL(function, CType)                                              \
    LIFT_INT_TO_NUMERAL_L(function, CType)                                                \
    LIFT_INT_TO_NUMERAL_R(function, CType)                                                \

    LIFT_INT_TO_NUMERAL(operator+, Numeral<C>)
    LIFT_INT_TO_NUMERAL(operator-, Numeral<C>)
    LIFT_INT_TO_NUMERAL(operator*, Numeral<C>)

    LIFT_INT_TO_NUMERAL(operator==, Numeral<C>)
    LIFT_INT_TO_NUMERAL(operator!=, Numeral<C>)
    LIFT_INT_TO_NUMERAL(operator<=, Numeral<C>)
    LIFT_INT_TO_NUMERAL(operator>=, Numeral<C>)
    LIFT_INT_TO_NUMERAL(operator< , Numeral<C>)
    LIFT_INT_TO_NUMERAL(operator> , Numeral<C>)

    LIFT_INT_TO_NUMERAL(operator+, Term<C>)
    LIFT_INT_TO_NUMERAL(operator-, Term<C>)
    LIFT_INT_TO_NUMERAL_L(operator*, Term<C>)


     // MULTIPLICATION
     // DIVISION

    template<class C>
    Term<C> operator/(Term<C> lhs, Numeral<C> rhs) 
    { return (1 / rhs) * lhs; }

    template<class C>
    Numeral<C> operator/(Numeral<C> lhs, Numeral<C> rhs) 
    { return Numeral<C>{ rhs.config, rhs.config->inverse(rhs.inner) } * lhs; }

    LIFT_INT_TO_NUMERAL_R(operator/, Term<C>)
    LIFT_INT_TO_NUMERAL(operator/, Numeral<C>)

     // MINUS

#define DEF_UMINUS(CType)                                                                 \
    template<class C> \
    CType operator-(CType x)                                                       \
    { return -1 * x; }                                                                    \

  DEF_UMINUS(Numeral<C>)
  DEF_UMINUS(Term<C>)

#define DEF_BMINUS(T1, T2)                                                                \
    template<class C> \
    auto operator-(T1 x, T2 y)                                                     \
    { return x + -y; }                                                                    \

    DEF_BMINUS(Numeral<C>, Numeral<C>)
    DEF_BMINUS(Term<C>   , Numeral<C>)
    DEF_BMINUS(Numeral<C>, Term<C>   )
    DEF_BMINUS(Term<C>   , Term<C>   )

     // ABS

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

    // COMPARISIONS

    template<class C>
    bool operator<=(Numeral<C> lhs, Numeral<C> rhs) 
    { return lhs.config->leq(lhs.inner, rhs.inner); }

    template<class C>
    bool operator<(Numeral<C> lhs, Numeral<C> rhs) 
    { return lhs.config->less(lhs.inner, rhs.inner); }

    template<class C>
    bool operator>=(Numeral<C> lhs, Numeral<C> rhs) 
    { return rhs <= lhs; }

    template<class C>
    bool operator>(Numeral<C> lhs, Numeral<C> rhs) 
    { return rhs < lhs; }

#define INT_CMP(OP)                                                                       \
    template<class C>                                                                \
    bool operator OP (Numeral<C> lhs, int rhs)                                       \
    { return lhs OP Numeral<C>  { lhs.config, lhs.config->numeral(rhs), }; }         \
                                                                                          \
    template<class C>                                                                \
    bool operator OP (int lhs, Numeral<C> rhs)                                       \
    { return Numeral<C>  { rhs.config, rhs.config->numeral(lhs), } OP rhs; }         \

    template<class C>
    Term<C> quot(Term<C> t, Numeral<C> p) { return floor(t / p); }

    template<class C>
    Term<C> rem(Term<C> t, Numeral<C> p) { return t - p * quot(t, p); }

    template<class C>
    Term<C> to_term(Numeral<C> n) 
    { return Term<C> { n.config, n.config->term(n.inner), }; }

    template<class C>
    Numeral<C> to_numeral(C* c, int n) 
    { return Numeral<C> { c, c->numeral(n), }; }

#define LIFT_NUMERAL_TO_TERM_L(fn)                                                        \
    template<class C>                                                                \
    auto fn(Numeral<C> const& lhs, Term<C> const& rhs)                          \
    { return fn(to_term(lhs), rhs); }

#define LIFT_NUMERAL_TO_TERM_R(fn)                                                        \
    template<class C>                                                                \
    auto fn(Term<C> const& lhs, Numeral<C> const& rhs)                          \
    { return fn(lhs, to_term(rhs)); }

#define LIFT_NUMERAL_TO_TERM(fn)                                                          \
    LIFT_NUMERAL_TO_TERM_L(fn)                                                            \
    LIFT_NUMERAL_TO_TERM_R(fn)                                                            \


#define LITERAL_CONSTRUCTION_OPERATOR(fn, Sym)                                            \
    template<class C>                                                                \
    Literal<C> fn(Term<C> lhs, Term<C> rhs)                                \
    {                                                                                     \
      VIRAS_ASSERT(lhs.config == rhs.config);                                             \
      return Literal<C> { lhs.config, lhs.config->create_literal((lhs - rhs).inner, Sym) }; \
    }                                                                                     \
                                                                                          \
    LIFT_NUMERAL_TO_TERM(fn)                                                              \
    LIFT_INT_TO_NUMERAL(fn, Term<C>)                                                 \

    LITERAL_CONSTRUCTION_OPERATOR(operator> , PredSymbol::Gt);
    LITERAL_CONSTRUCTION_OPERATOR(operator>=, PredSymbol::Geq);
    LITERAL_CONSTRUCTION_OPERATOR(eq, PredSymbol::Neq);
    LITERAL_CONSTRUCTION_OPERATOR(neq, PredSymbol::Eq);

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
      return matchTerm(self, 
        /* var y */     [&](auto v)         { return v == var ? by : self; }, 
        /* numeral 1 */ [&]()               { return self; }, 
        /* k * t */     [&](auto k, auto t) { return k * subs(t, var, by); }, 
        /* l + r */     [&](auto l, auto r) { return subs(l,var,by) + subs(r,var,by); }, 
        /* floor */     [&](auto t)         { return floor(subs(t,var,by)); });
    }


} // namespace viras
} // namespace sugar
