#pragma once
#include "viras/base_types.h"
#include "viras/virtual_term.h"
#include "viras/iter.h"
#include "viras/break.h"

namespace viras {

  template<class C>
  struct LiraTerm {
    // C* config;
    Term<C> self;
    Var<C> x;
    Term<C> lim;
    Numeral<C> sslp;
    Numeral<C> oslp;
    Numeral<C> per;
    Numeral<C> deltaY;
    Term<C> distYminus;
    Term<C> distYplus() { return distYminus + deltaY; }
    std::vector<Break<C>> breaks;

    Term<C> distXminus() const {
      return -(1 / oslp) * (oslp > 0 ? distYminus + deltaY
                                     : distYminus         );
    }

    Term<C> distXplus() const { 
      return  -(1 / oslp) * (oslp > 0 ? distYminus
                                      : distYminus + deltaY);

    }

    // Numeral<C> deltaX() const { return viras_eval_numeral(config, abs(1/oslp) * deltaY); }
    Numeral<C> deltaX() const { return abs(1/oslp) * deltaY; }
    Term<C> lim_at(Term<C> x0) const { return subs(lim, x, x0); }
    Term<C> dseg(Term<C> x0) const { return -(sslp * x0) + lim_at(x0); }
    Term<C> zero(Term<C> x0) const { return x0 - lim_at(x0) / sslp; }
    bool periodic() const { return oslp == 0; }

    friend std::ostream& operator<<(std::ostream& out, LiraTerm const& self)
    { return out << self.self; }

    template<class MatchRec>
    static Term<C> calcLim(LiraTerm const& self, Var<C> const& x, MatchRec matchRec) {
       return matchRec(
        /* var y */ [&](auto y) 
        { return self.self; },

        /* numeral 1 */ [&]() 
        { return self.self; },

        /* k * t */ [&](auto k, auto t, auto& rec) 
        { return rec.per == 0 ? self.self : k * rec.lim; },

        /* l + r */ [&](auto l, auto r, auto& rec_l, auto& rec_r) 
        { return self.per == 0 ? self.self : rec_l.lim + rec_r.lim; },

        /* floor t */   [&](auto t, auto& rec) 
        { return self.per == 0      ? self.self
               : rec.sslp >= 0 ? floor(rec.lim) 
                                 : ceil(rec.lim) - 1; }
        );
    }


    template<class MatchRec>
    static Numeral<C> calcPer(LiraTerm const& self, Var<C> const& x, MatchRec matchRec) {
      auto to_numeral = [&](auto n) { return viras::to_numeral(self.self.config, n); };
       return matchRec(
        /* var y */ [&](auto y) 
        { return to_numeral(0); },

        /* numeral 1 */ [&]() 
        { return to_numeral(0); },

        /* k * t */ [&](auto k, auto t, auto& rec) 
        { return rec.per; },

        /* l + r */ [&](auto l, auto r, auto& rec_l, auto& rec_r) 
        { return rec_l.per == 0 ? rec_r.per
               : rec_r.per == 0 ? rec_l.per
               : lcm(rec_l.per, rec_r.per); },

        /* floor t */   [&](auto t, auto& rec) 
        { return rec.per == 0 && rec.oslp == 0 ? to_numeral(0)
               : rec.per == 0                  ? 1 / abs(rec.oslp)
               : num(rec.per) * den(rec.oslp); }
        );
    }

    template<class MatchRec>
    static Numeral<C> calcSslp(LiraTerm const& self, Var<C> const& x, MatchRec matchRec) {
      auto to_numeral = [&](auto n) { return viras::to_numeral(self.self.config, n); };
      return matchRec(
        /* var y */ [&](auto y) 
        { return to_numeral(y == x ? 1 : 0); }

        /* numeral 1 */ , [&]() 
        { return to_numeral(0); }

        /* k * t */ , [&](auto k, auto t, auto& rec) 
        { return k * rec.sslp; }

        /* l + r */ , [&](auto l, auto r, auto& rec_l, auto& rec_r) 
        { return rec_l.sslp + rec_r.sslp; }

        /* floor t */ , [&](auto t, auto& rec) 
        { return to_numeral(0); }
        );
    }


    template<class MatchRec>
    static Numeral<C> calcOslp(LiraTerm const& self, Var<C> const& x, MatchRec matchRec) {
      auto to_numeral = [&](auto n) { return viras::to_numeral(self.self.config, n); };
      return matchRec(
        /* var y */ [&](auto y) 
        { return to_numeral(y == x ? 1 : 0); }

        /* numeral 1 */ , [&]() 
        { return to_numeral(0); }

        /* k * t */ , [&](auto k, auto t, auto& rec) 
        { return k * rec.oslp; }

        /* l + r */ , [&](auto l, auto r, auto& rec_l, auto& rec_r) 
        { return rec_l.oslp + rec_r.oslp; }

        /* floor t */ , [&](auto t, auto& rec) 
        { return rec.oslp; }
      );
    }


    template<class MatchRec>
    static Numeral<C> calcDeltaY(LiraTerm const& self, Var<C> const& x, MatchRec matchRec) {
      auto to_numeral = [&](auto n) { return viras::to_numeral(self.self.config, n); };
       return matchRec(
        /* var y */ [&](auto y) 
        { return to_numeral(0); }

        /* numeral 1 */ , [&]() 
        { return to_numeral(0); }

        /* k * t */ , [&](auto k, auto t, auto& rec) 
        { return abs(k) * rec.deltaY; }

        /* l + r */ , [&](auto l, auto r, auto& rec_l, auto& rec_r) 
        { return rec_l.deltaY + rec_r.deltaY; }

        /* floor t */ , [&](auto t, auto& rec)  {
          VIRAS_ASSERT(self.per != 0 || rec.per == 0);
          return C::optimizeBounds 
               ? (self.per == 0 ? to_numeral(0) : rec.deltaY + 1)
               :                                rec.deltaY + 1 ; 
        }
        );
    }


    template<class MatchRec>
    static Term<C> calcDistYminus(LiraTerm const& self, Var<C> const& x, MatchRec matchRec) {
      auto n_term = [&](auto n) { return viras::to_term(self.self.config, n); };
       return matchRec(
        /* var y */ [&](auto y) 
        { return y == x ? n_term(0) : to_term(y); }

        /* numeral 1 */ , [&]() 
        { return n_term(1); }

        /* k * t */ , [&](auto k, auto t, auto& rec) 
        { return k >= 0 ? k * rec.distYminus : k * rec.distYplus(); }

        /* l + r */ , [&](auto l, auto r, auto& rec_l, auto& rec_r) 
        { return rec_l.distYminus + rec_r.distYminus; }

        /* floor t */ , [&](auto t, auto& rec) 
        { 
          VIRAS_ASSERT(self.per != 0 || rec.per == 0);
          return C::optimizeBounds 
               ? (self.per == 0 ? floor(rec.distYminus) :  rec.distYminus - 1)
               :                                           rec.distYminus - 1 ; }
        );
    }


    template<class MatchRec>
    static std::vector<Break<C>> calcBreaks(LiraTerm const& self, Var<C> const& x, MatchRec matchRec) {
      auto n_term = [&](auto n) { return viras::to_term(self.self.config, n); };
      return matchRec(
        /* var y */ [&](auto y) 
        { return std::vector<Break<C>>(); }

        /* numeral 1 */ , [&]() 
        { return std::vector<Break<C>>(); }

        /* k * t */ , [&](auto k, auto t, auto& rec) 
        { return std::move(rec.breaks); }

        /* l + r */ , [&](auto l, auto r, auto& rec_l, auto& rec_r)  {
          auto breaks = std::move(rec_l.breaks);
          breaks.insert(breaks.end(), rec_r.breaks.begin(), rec_r.breaks.end());
          return breaks;
        }

        /* floor t */ , [&](auto t, auto& rec)  {
          if (rec.sslp == 0) {
            return std::move(rec.breaks);
          } else if (rec.breaks.empty()) {
            return std::vector<Break<C>>{Break<C>(rec.zero(n_term(0)), self.per)};
          } else {
            auto p_min = *(iter::array(rec.breaks) 
              | iter::map([](auto b) -> Numeral<C> { return b->p; })
              | iter::min);
            auto breaks = std::vector<Break<C>>();
            for ( auto b0p_pZ : rec.breaks ) {
              auto b0p = b0p_pZ.t;
              auto p   = b0p_pZ.p;
              intersectGrid(b0p_pZ, 
                            Bound::Closed, b0p, self.per, Bound::Open) 
                | iter::foreach([&](auto b0) {
                    intersectGrid(Break<C>(rec.zero(b0), 1/abs(rec.sslp)), 
                                  Bound::Closed, b0, p_min, Bound::Open)
                      | iter::foreach([&](auto b) {
                          breaks.push_back(Break<C>(b, self.per));
                      });
                });
            }
            breaks.insert(breaks.end(), rec.breaks.begin(), rec.breaks.end());
            return breaks;
          }
        }
      );
    }


    static LiraTerm analyse(Term<C> self, Var<C> x) {
      LiraTerm rec0;
      LiraTerm rec1;
      matchTerm(self, 
        /* var v */ [&](auto y) { return std::make_tuple(); }, 
        /* numeral 1 */ [&]() { return std::make_tuple(); }, 
        /* k * t */ [&](auto k, auto t) { 
          rec0 = analyse(t, x);
          return std::make_tuple();
        }, 

        /* l + r */ [&](auto l, auto r) { 
          rec0 = analyse(l, x);
          rec1 = analyse(r, x);
          return std::make_tuple();
        }, 

        /* floor */ [&](auto t) { 
          rec0 = analyse(t, x);
          return std::make_tuple();
        });
      auto matchRec = [&](auto if_var, auto if_one, auto if_mul, auto if_add, auto if_floor) {
        return matchTerm(self, 
        /* var v */ if_var,
        /* numeral 1 */ if_one,
        /* k * t */ [&](auto k, auto t) { return if_mul(k, t, rec0); }, 
        /* l + r */ [&](auto l, auto r) { return if_add(l, r, rec0, rec1); }, 
        /* floor */ [&](auto t) { return if_floor(t, rec0); });
      };
      LiraTerm res;
      res.self = self;
      res.x = x;
      res.per = calcPer(res, x, matchRec);
      res.lim = calcLim(res, x, matchRec);
      res.sslp = calcSslp(res, x, matchRec);
      res.oslp = calcOslp(res, x, matchRec);
      res.deltaY = calcDeltaY(res, x, matchRec);
      res.distYminus = calcDistYminus(res, x, matchRec);
      res.breaks = calcBreaks(res, x, matchRec);
      
#define DEBUG_FIELD(field)                                                                \
        DBG("analyse(", res.self, ")." #field " = ", res.field)
        // DEBUG_FIELD(breaks.size())
        // iter::array(res.breaks) | iter::dbg("break") | iter::foreach([](auto...){});
        // DBG("")
        // DEBUG_FIELD(per)
        // DEBUG_FIELD(deltaY)
        // DBG("")

        if (C::optimizeBounds) {
          VIRAS_ASSERT(res.per != 0 || res.deltaY == 0);
        }
        VIRAS_ASSERT((res.per == 0) == (res.breaks.size() == 0));
        return res;
    }


  };


} // namespace viras
