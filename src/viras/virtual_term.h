#pragma once
#include "viras/config_macros.h"
#include "viras/base_types.h"
#include "viras/break.h"

namespace viras {
    
  struct Epsilon {
    friend std::ostream& operator<<(std::ostream& out, Epsilon const& self)
    { return out << "ε"; }
    DERIVE_TUPLE(Epsilon,)
    DERIVE_TUPLE_EQ
    DERIVE_TUPLE_LESS
  };

  struct Infty {
    bool positive;
    Infty operator-() const 
    { return Infty { .positive = !positive, }; }

    friend std::ostream& operator<<(std::ostream& out, Infty const& self)
    { 
      if (self.positive) {
        return out << "∞";
      } else {
        return out << "-∞";
      }
    }
    DERIVE_TUPLE(Infty, positive)
    DERIVE_TUPLE_EQ
    DERIVE_TUPLE_LESS
  };


  template<class C>
  struct ZComp {
    Numeral<C> period;

    explicit ZComp(Numeral<C> period) : period(period) {}

    friend std::ostream& operator<<(std::ostream& out, ZComp const& self)
    { return out << self.period << "ℤ"; }
    DERIVE_TUPLE(ZComp, period)
    DERIVE_TUPLE_EQ
    DERIVE_TUPLE_LESS
  };


  template<class C>
  struct VirtualTerm {
    std::optional<Term<C>> term;
    std::optional<Epsilon> epsilon;
    std::optional<Numeral<C>> period;
    std::optional<Infty> infty;
  public:
    VirtualTerm(
      std::optional<Term<C>> term,
      std::optional<Epsilon> epsilon,
      std::optional<Numeral<C>> period,
      std::optional<Infty> infinity) 
      : term(std::move(term))
      , epsilon(std::move(epsilon))
      , period(std::move(period))
      , infty(std::move(infinity))
    {
      VIRAS_ASSERT(term || infinity);
      VIRAS_ASSERT(!infty || !period);
    }

    VirtualTerm(Numeral<C> n) : VirtualTerm(to_term(n)) {}
    VirtualTerm(Break<C> t_pZ) : VirtualTerm(std::move(t_pZ.t), {}, std::move(t_pZ.p), {}) {}
    VirtualTerm(Infty infty) : VirtualTerm({}, {}, {}, infty) {}
    VirtualTerm(Term<C> t) : VirtualTerm(std::move(t), {}, {}, {}) {}

    static VirtualTerm periodic(Term<C> b, Numeral<C> p) { return VirtualTerm(std::move(b), {}, std::move(p), {}); }

    friend std::ostream& operator<<(std::ostream& out, VirtualTerm const& self)
    { 
      bool fst = true;
#define __OUTPUT(field)                                                                   \
      if (fst) { out << field; fst = false; }                                             \
      else { out << " + " << field; }                                                     \

      if (self.term) { __OUTPUT(*self.term) }
      if (self.epsilon) { __OUTPUT(*self.epsilon) }
      if (self.period) { __OUTPUT(*self.period << " ℤ") }
      if (self.infty) { __OUTPUT(*self.infty) }
#undef __OUTPUT
      if (fst) { out << "0"; fst = false; }
      return out; 
    }

    DERIVE_TUPLE(VirtualTerm, term, epsilon, period, infty)
    DERIVE_TUPLE_EQ
    DERIVE_TUPLE_LESS
  };

  namespace sugar {
    template<class C>
    VirtualTerm<C> operator+(VirtualTerm<C> const& t, Epsilon const& e)
    { 
      VirtualTerm<C> out = t;
      out.epsilon = std::optional<Epsilon>(e);
      return out; 
    }

    template<class C>
    VirtualTerm<C> operator+(VirtualTerm<C> const& t, ZComp<C> const& z) 
    { 
      VirtualTerm<C> out = t;
      out.period = std::optional<Numeral<C>>(z.period);
      return out; 
    }

    template<class C>
    VirtualTerm<C> operator+(VirtualTerm<C> const& t, Infty const& i) 
    { 
      VirtualTerm<C> out = t;
      out.infty = std::optional<Infty>(i);
      return out; 
    }

#define LIFT_VIRTUAL_TERM_PLUS(Type)                                                      \
    template<class C>                                                                     \
    VirtualTerm<C> operator+(Term<C> const& t, Type const& x)                      \
    { return VirtualTerm<C>(t) + x; }                                                     \
                                                                                          \
    template<class C>                                                                     \
    VirtualTerm<C> operator+(Numeral<C> const& t, Type const& x)                   \
    { return to_term(t) + x; }                                                     \

    LIFT_VIRTUAL_TERM_PLUS(Epsilon);
    LIFT_VIRTUAL_TERM_PLUS(ZComp<C>);
    LIFT_VIRTUAL_TERM_PLUS(Infty);

    template<class C>
    VirtualTerm<C> operator+(int t, ZComp<C> const& z) 
    { return to_numeral(z.period.config, t) + z; }

  } // namespace sugar

} // namespace viras
