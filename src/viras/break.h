#pragma once
#include "viras/base_types.h"
#include "viras/iter.h"

namespace viras {

  template<class C>
  struct Break {
    Term<C> t;
    Numeral<C> p;
    Break(Term<C> t, Numeral<C> p) : t(t), p(p) { VIRAS_ASSERT(p > 0) }
    friend std::ostream& operator<<(std::ostream& out, Break const& self)
    { return out << self.t << " + " << self.p << "ℤ"; }
    DERIVE_TUPLE(Break,t,p)
    DERIVE_TUPLE_EQ
  };


  enum class Bound {
    Open,
    Closed,
  };

  template<class C>
  Term<C> grid_ceil (Term<C> t, Break<C> s_pZ) { return t + rem(s_pZ.t - t, s_pZ.p); }
  template<class C>
  Term<C> grid_floor(Term<C> t, Break<C> s_pZ) { return t - rem(t - s_pZ.t, s_pZ.p); }

  template<class C>
  auto intersectGrid(Break<C> s_pZ, Bound l, Term<C> t, Numeral<C> k, Bound r) {
    auto p = s_pZ.p;
    auto start = [&]() {
      switch(l) {
        case Bound::Open:   return grid_floor(t + p, s_pZ);
        case Bound::Closed: return grid_ceil(t, s_pZ);
      };
    }();
    VIRAS_ASSERT(k != 0 || (l == Bound::Closed && r == Bound::Closed));
    return iter::if_then_(t.config->opts.optimizeGridIntersection() && k == 0, iter::vals(start))
                 else____(iter::nat_iter(to_numeral(t.config, 0))
                            | iter::take_while([r,p,k](auto n) -> bool { 
                                switch(r) {
                                  case Bound::Open:   return n * p < k; 
                                  case Bound::Closed: return n * p <= k; 
                                }
                              })
                            | iter::map([start, p](auto n) {
                              return start + p * n;
                              }));
                 
  }


} // namespace viras
