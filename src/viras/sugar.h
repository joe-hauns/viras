#pragma once

#include "viras/output.h"
#include "viras/predicate.h"
#include "viras/derive.h"

namespace viras {
namespace sugar {


    template<class Config, class T>
    struct WithConfig { 
      Config* config; 
      T inner; 

      friend bool operator!=(WithConfig l, WithConfig r) 
      { return !(l == r); }

      friend std::ostream& operator<<(std::ostream& out, WithConfig const& self)
      { return out << output::ptr(self.inner); }

      DERIVE_TUPLE(WithConfig, inner)
      DERIVE_TUPLE_EQ
      DERIVE_TUPLE_LESS
    };

    template<class Config> struct Term    : public WithConfig<Config, typename Config::Term   > {};
    template<class Config> struct Numeral : public WithConfig<Config, typename Config::Numeral> {};
    template<class Config> struct Var     : public WithConfig<Config, typename Config::Var    > {};
    template<class Config> struct Literal : public WithConfig<Config, typename Config::Literal> {
      Term<Config> term() const
      { return Term<Config> {this->config, this->config->term_of_literal(this->inner)}; }

      PredSymbol symbol() const
      { return this->config->symbol_of_literal(this->inner); }

      friend std::ostream& operator<<(std::ostream& out, Literal<Config> const& self)
      { return out << self.term() << " " << self.symbol() << " 0"; }
    };
    template<class Config>
    struct Literals : public WithConfig<Config, typename Config::Literals> {
      auto size() const { return this->config->literals_size(this->inner); }
      auto operator[](size_t idx) const { 
        return Literal<Config> { this->config, this->config->literals_get(this->inner, idx) }; 
      }
    };

    ///////////////////////////////////////
    // PRIMARY OPERATORS
    ///////////////////////////////////////

    template<class Config>
    Term<Config> operator+(Term<Config> lhs, Term<Config> rhs) 
    {
      VIRAS_ASSERT(lhs.config == rhs.config);
      return Term<Config> {lhs.config, lhs.config->add(lhs.inner, rhs.inner)};
    }

    template<class Config>
    Term<Config> operator*(Numeral<Config> lhs, Term<Config> rhs) 
    {
      VIRAS_ASSERT(lhs.config == rhs.config);
      return Term<Config> {lhs.config, lhs.config->mul(lhs.inner, rhs.inner)};
    }

    template<class Config>
    Numeral<Config> operator*(Numeral<Config> lhs, Numeral<Config> rhs) 
    {
      VIRAS_ASSERT(lhs.config == rhs.config);
      return Numeral<Config> {lhs.config, lhs.config->mul(lhs.inner, rhs.inner)};
    }

    ///////////////////////////////////////
    // LIFTED OPERATORS
    ///////////////////////////////////////

    template<class Config>
    Numeral<Config> operator+(Numeral<Config> lhs, Numeral<Config> rhs) 
    { return Numeral<Config> { lhs.config, lhs.config->add(lhs.inner, rhs.inner)}; }

    template<class Config>
    Term<Config> operator+(Numeral<Config> lhs, Term<Config> rhs) 
    { return Term<Config> { rhs.config, lhs.config->term(lhs.inner)} + rhs; }

    template<class Config>
    Term<Config> operator+(Term<Config> lhs, Numeral<Config> rhs) 
    { return lhs + Term<Config> { rhs.config, rhs.config->term(rhs.inner), }; }

#define LIFT_INT_TO_NUMERAL(function, CType)                                              \
    LIFT_INT_TO_NUMERAL_L(function, CType)                                                \
    LIFT_INT_TO_NUMERAL_R(function, CType)                                                \


#define LIFT_INT_TO_NUMERAL_L(function, CType)                                            \
    template<class Config>                                                                \
    auto function(int lhs, CType rhs)                                                     \
    { return function(Numeral<Config> {rhs.config, rhs.config->numeral(lhs)}, rhs); }     \

#define LIFT_INT_TO_NUMERAL_R(function, CType)                                            \
    template<class Config>                                                                \
    auto function(CType lhs, int rhs)                                                     \
    { return function(lhs, Numeral<Config> {lhs.config, lhs.config->numeral(rhs)}); }     \

#define LIFT_INT_TO_NUMERAL(function, CType)                                              \
    LIFT_INT_TO_NUMERAL_L(function, CType)                                                \
    LIFT_INT_TO_NUMERAL_R(function, CType)                                                \

    LIFT_INT_TO_NUMERAL(operator+, Numeral<Config>)
    LIFT_INT_TO_NUMERAL(operator-, Numeral<Config>)
    LIFT_INT_TO_NUMERAL(operator*, Numeral<Config>)

    LIFT_INT_TO_NUMERAL(operator==, Numeral<Config>)
    LIFT_INT_TO_NUMERAL(operator!=, Numeral<Config>)
    LIFT_INT_TO_NUMERAL(operator<=, Numeral<Config>)
    LIFT_INT_TO_NUMERAL(operator>=, Numeral<Config>)
    LIFT_INT_TO_NUMERAL(operator< , Numeral<Config>)
    LIFT_INT_TO_NUMERAL(operator> , Numeral<Config>)

    LIFT_INT_TO_NUMERAL(operator+, Term<Config>)
    LIFT_INT_TO_NUMERAL(operator-, Term<Config>)
    LIFT_INT_TO_NUMERAL_L(operator*, Term<Config>)


     // MULTIPLICATION
     // DIVISION

    template<class Config>
    Term<Config> operator/(Term<Config> lhs, Numeral<Config> rhs) 
    { return (1 / rhs) * lhs; }

    template<class Config>
    Numeral<Config> operator/(Numeral<Config> lhs, Numeral<Config> rhs) 
    { return Numeral<Config>{ rhs.config, rhs.config->inverse(rhs.inner) } * lhs; }

    LIFT_INT_TO_NUMERAL_R(operator/, Term<Config>)
    LIFT_INT_TO_NUMERAL(operator/, Numeral<Config>)

     // MINUS

#define DEF_UMINUS(CType)                                                                 \
    template<class Config> \
    CType operator-(CType x)                                                       \
    { return -1 * x; }                                                                    \

  DEF_UMINUS(Numeral<Config>)
  DEF_UMINUS(Term<Config>)

#define DEF_BMINUS(T1, T2)                                                                \
    template<class Config> \
    auto operator-(T1 x, T2 y)                                                     \
    { return x + -y; }                                                                    \

    DEF_BMINUS(Numeral<Config>, Numeral<Config>)
    DEF_BMINUS(Term<Config>   , Numeral<Config>)
    DEF_BMINUS(Numeral<Config>, Term<Config>   )
    DEF_BMINUS(Term<Config>   , Term<Config>   )

     // ABS

    template<class Config>
    Numeral<Config> abs(Numeral<Config> x) 
    { return x < 0 ? -x : x; }

    template<class Config>
    Numeral<Config> num(Numeral<Config> x)
    { return Numeral<Config> { x.config, x.config->num(x.inner) }; }

    template<class Config>
    Numeral<Config> den(Numeral<Config> x) 
    { return Numeral<Config> { x.config, x.config->den(x.inner) }; }

    template<class Config>
    Numeral<Config> lcm(Numeral<Config> l, Numeral<Config> r)
    { 
      auto cn = [&](auto x) { return Numeral<Config> { l.config, x }; };
      return cn(l.config->lcm(num(l).inner, num(r).inner)) 
           / cn(l.config->gcd(den(l).inner, den(r).inner));  
    }

     // floor
    template<class Config>
    Term<Config> floor(Term<Config> x) 
    { return Term<Config> { x.config, x.config->floor(x.inner), }; }

    template<class Config>
    Term<Config> ceil(Term<Config> x) 
    { return -floor(-x); }


    template<class Config>
    Numeral<Config> floor(Numeral<Config> x) 
    { return Numeral<Config> { x.config, x.config->floor(x.inner), }; }

    // COMPARISIONS

    template<class Config>
    bool operator<=(Numeral<Config> lhs, Numeral<Config> rhs) 
    { return lhs.config->leq(lhs.inner, rhs.inner); }

    template<class Config>
    bool operator<(Numeral<Config> lhs, Numeral<Config> rhs) 
    { return lhs.config->less(lhs.inner, rhs.inner); }

    template<class Config>
    bool operator>=(Numeral<Config> lhs, Numeral<Config> rhs) 
    { return rhs <= lhs; }

    template<class Config>
    bool operator>(Numeral<Config> lhs, Numeral<Config> rhs) 
    { return rhs < lhs; }

#define INT_CMP(OP)                                                                       \
    template<class Config>                                                                \
    bool operator OP (Numeral<Config> lhs, int rhs)                                       \
    { return lhs OP Numeral<Config>  { lhs.config, lhs.config->numeral(rhs), }; }         \
                                                                                          \
    template<class Config>                                                                \
    bool operator OP (int lhs, Numeral<Config> rhs)                                       \
    { return Numeral<Config>  { rhs.config, rhs.config->numeral(lhs), } OP rhs; }         \

    template<class Config>
    Term<Config> quot(Term<Config> t, Numeral<Config> p) { return floor(t / p); }

    template<class Config>
    Term<Config> rem(Term<Config> t, Numeral<Config> p) { return t - p * quot(t, p); }

    template<class Config>
    Term<Config> to_term(Numeral<Config> n) 
    { return Term<Config> { n.config, n.config->term(n.inner), }; }

    template<class Config>
    Numeral<Config> to_numeral(Config* c, int n) 
    { return Numeral<Config> { c, c->numeral(n), }; }

#define LIFT_NUMERAL_TO_TERM_L(fn)                                                        \
    template<class Config>                                                                \
    auto fn(Numeral<Config> const& lhs, Term<Config> const& rhs)                          \
    { return fn(to_term(lhs), rhs); }

#define LIFT_NUMERAL_TO_TERM_R(fn)                                                        \
    template<class Config>                                                                \
    auto fn(Term<Config> const& lhs, Numeral<Config> const& rhs)                          \
    { return fn(lhs, to_term(rhs)); }

#define LIFT_NUMERAL_TO_TERM(fn)                                                          \
    LIFT_NUMERAL_TO_TERM_L(fn)                                                            \
    LIFT_NUMERAL_TO_TERM_R(fn)                                                            \


#define LITERAL_CONSTRUCTION_OPERATOR(fn, Sym)                                            \
    template<class Config>                                                                \
    Literal<Config> fn(Term<Config> lhs, Term<Config> rhs)                                \
    {                                                                                     \
      VIRAS_ASSERT(lhs.config == rhs.config);                                             \
      return Literal<Config> { lhs.config, lhs.config->create_literal((lhs - rhs).inner, Sym) }; \
    }                                                                                     \
                                                                                          \
    LIFT_NUMERAL_TO_TERM(fn)                                                              \
    LIFT_INT_TO_NUMERAL(fn, Term<Config>)                                                 \

    LITERAL_CONSTRUCTION_OPERATOR(operator> , PredSymbol::Gt);
    LITERAL_CONSTRUCTION_OPERATOR(operator>=, PredSymbol::Geq);
    LITERAL_CONSTRUCTION_OPERATOR(eq, PredSymbol::Neq);
    LITERAL_CONSTRUCTION_OPERATOR(neq, PredSymbol::Eq);

    template<class Config, class IfVar, class IfOne, class IfMul, class IfAdd, class IfFloor>
    auto matchTerm(Term<Config> t, 
        IfVar   if_var, 
        IfOne   if_one, 
        IfMul   if_mul, 
        IfAdd   if_add, 
        IfFloor if_floor
        ) -> decltype(auto) {
      return t.config->matchTerm(t.inner,
        [&](auto x) { return if_var(Var<Config> { t.config, x }); }, 
        [&]() { return if_one(); }, 
        [&](auto l, auto r) { return if_mul(Numeral<Config> {t.config, l},Term<Config>{t.config, r}); }, 
        [&](auto l, auto r) { return if_add(Term<Config>{t.config, l},Term<Config>{t.config, r}); }, 
        [&](auto x) { return if_floor(Term<Config>{t.config, x}); }
           );
    }


    template<class Config>
    Term<Config> subs(Term<Config> self, Var<Config> var, Term<Config> by) {
      return matchTerm(self, 
        /* var y */     [&](auto v)         { return v == var ? by : self; }, 
        /* numeral 1 */ [&]()               { return self; }, 
        /* k * t */     [&](auto k, auto t) { return k * subs(t, var, by); }, 
        /* l + r */     [&](auto l, auto r) { return subs(l,var,by) + subs(r,var,by); }, 
        /* floor */     [&](auto t)         { return floor(subs(t,var,by)); });
    }


} // namespace viras
} // namespace sugar
