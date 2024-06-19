#pragma once
#include "viras/config.h"
#include "viras/output.h"
#include "viras/iter.h"
#include "viras/derive.h"
#include "viras/sugar.h"

#include <map>
#include <tuple>

namespace viras {


  template<class Config>
  struct SimplifyingConfig {
    Config config;

    SimplifyingConfig(Config c): config(std::move(c)) {}

    using Literals = typename Config::Literals;
    using Literal  = typename Config::Literal;
    using Var      = typename Config::Var;
    using Term     = typename Config::Term;
    using Numeral  = typename Config::Numeral;

    Numeral numeral(int i) { return config.numeral(i); }
    Numeral lcm(Numeral l, Numeral r) { return config.lcm(l, r); }
    Numeral gcd(Numeral l, Numeral r) { return config.gcd(l, r); }

    Numeral mul(Numeral l, Numeral r) { return config.mul(l,r); }
    Numeral add(Numeral l, Numeral r) { return config.add(l,r); }
    Numeral floor(Numeral t) { return config.floor(t); }

    Term simpl(Term self) { 
      auto dflt = [&](auto...) { return self; };
      return matchTerm(self, 
        /* var v */ dflt,
        /* numeral 1 */ dflt,
        /* k * t */ [&](auto k, auto t) { return mul(k, simpl(t)); }, 
        /* l + r */ [&](auto l, auto r) { return add(simpl(l), simpl(r)); }, 
        /* floor */ [&](auto t) { return floor(simpl(t)); }
        );
    }

    Term term(Numeral n) { return config.term(n); }
    Term term(Var v) { return config.term(v); }

    Term mul(Numeral l, Term r) { 
      auto dflt = [&](auto...) { return config.mul(l,r); };
      return
             l == numeral(0) ? term(numeral(0))
           : l == numeral(1) ? r
           : matchTerm(r, 
             /* var v */ dflt, 

             /* numeral 1 */ [&]() { return term(l); }, 
             /* k * t */ [&](auto k, auto t) { return mul(mul(l, k), t); }, 

             /* l + r */ [&](auto r0, auto r1) { return add(mul(l, r0), mul(l, r1)); }, 

             /* floor */ dflt);
    }

    bool isOne(Term t) { 
      return matchTerm(t, 
      /* var v */ [&](auto y) { return false; }, 
      /* numeral 1 */ [&]() { return true; }, 
      /* k * t */ [&](auto k, auto t) { return false; }, 
      /* l + r */ [&](auto l, auto r) { return false; }, 
      /* floor */ [&](auto t) { return false; }
      ); 
    }

    bool isZero(Term t) { 
      return matchTerm(t, 
      /* var v */ [&](auto y) { return false; }, 
      /* numeral 1 */ [&]() { return false; }, 
      /* k * t */ [&](auto k, auto t) { return k == numeral(0); }, 
      /* l + r */ [&](auto l, auto r) { return false; }, 
      /* floor */ [&](auto t) { return false; }
      ); 
    }

    Var test_var(const char* name) { return config.test_var(name); }

    std::optional<Numeral> tryNumeral(Term t) { 
      return matchTerm(t, 
        /* var v */ [&](auto y) { return std::optional<Numeral>(); }, 
        /* numeral 1 */ [&]() { return std::optional<Numeral>(numeral(1)); }, 
        /* k * t */ [&](auto k, auto t) { 
          return isOne(t) ? std::optional<Numeral>(k)
                          : std::optional<Numeral>();
        }, 
        /* l + r */ [&](auto l, auto r) { return std::optional<Numeral>(); }, 
        /* floor */ [&](auto t) { return std::optional<Numeral>(); }); 
    };

    template<class F>
    void __for_monom(Term const& self, F& f, Numeral& prod) {
      auto dflt = [&](auto...args){ f(prod, self); return std::make_tuple(); };
      matchTerm(self, 
        /* var v */ dflt, 

        /* numeral 1 */ dflt,
        /* k * t */ [&](auto k, auto t) { 
          if (k != numeral(0)) {
            prod = prod * k;
            __for_monom(t, f, prod);
            prod = prod / k;
          }
          return std::make_tuple(); 
        }, 
        // /* k * t */ [&](auto k, auto t) { f(k, t);  return std::make_tuple(); }, 

        /* l + r */ [&](auto l, auto r) { 
          __for_monom(l, f, prod);
          __for_monom(r, f, prod);
          return std::make_tuple();
        }, 

        /* floor */ dflt
        );
    }


    template<class F>
    void for_monom(Term self, F f) {
      auto prod = numeral(1);
      __for_monom(self, f, prod);
    }

    template<class Iter>
    Term iterToSum(Iter iter) {
      auto res = std::move(iter)
        | iter::filter([this](auto& pair)  { return pair->second != numeral(0); })
        | iter::map([this](auto pair) { return this->mul(pair->second, pair->first); })
        | iter::fold([this](auto l, auto r) { return config.add(l, r); });
      return res ? *res : config.term(config.numeral(0));
    }

    Term add(Term l, Term r) { 

      std::map<Term, Numeral> summands;
      auto addUp = [&](auto t) {
        for_monom(t, [&](Numeral n, Term t) {
            auto res_iter = summands.insert(std::make_pair(t, numeral(0))).first;
            auto& res = (*res_iter).second;
            res = config.add(res, n);
        });
      };
      addUp(l);
      addUp(r);

      return iterToSum(iter::stl(summands));
    }

    Term floor(Term t) { 
      std::map<Term, Numeral> outer;
      std::map<Term, Numeral> inner;

      auto update = [&](auto& map, auto key, auto f) {
        auto iter = map.insert(std::make_tuple(key,numeral(0))).first;
        auto& val = iter->second;
        val = f(val);
      };
      for_monom(t, [&](Numeral l, Term r) {
          auto integral = matchTerm(r, 
            /* var v */     [&](auto...) {                return false; }, 
            /* numeral 1 */ [&](auto...) {                return true;  }, 
            /* k * t */     [&](auto...) { VIRAS_ASSERT(false); return false; }, 
            /* l + r */     [&](auto...) { VIRAS_ASSERT(false); return false; }, 
            /* floor */     [&](auto...) {                return true;  });
          if (integral) {
            update(outer, r, [&](auto i)  { return i +      config.floor(l) ; });
            update(inner, r, [&](auto i) { return i + (l - config.floor(l)); });
          } else {
            update(inner, r, [&](auto i) { return i + l; });
          }
      });

      auto in_t = iterToSum(iter::stl(inner));
      auto num = tryNumeral(in_t);
      if (num) {
        auto fnum = config.floor(*num);
        if (fnum != numeral(0)) {
          update(outer, term(numeral(1)), [&](auto n) { return n + fnum; });
        }
      } else {
        update(outer, config.floor(in_t), [&](auto n) { return n + numeral(1); });
      }
      return iterToSum(iter::stl(outer));
    }

    Numeral inverse(Numeral n) { return config.inverse(n); }

    bool less(Numeral l, Numeral r) { return config.less(l,r); }
    bool leq(Numeral l, Numeral r) { return config.leq(l,r); }

    PredSymbol symbol_of_literal(Literal l) 
    { return config.symbol_of_literal(l); }

    Term term_of_literal(Literal l)
    { return config.term_of_literal(l); }

    Literal create_literal(Term t, PredSymbol s) { return config.create_literal(t,s); }

    Numeral num(Numeral l) { return config.num(l); }

    Numeral den(Numeral l) { return config.den(l); }

    size_t literals_size(Literals const& l) { return config.literals_size(l); }
    Literal literals_get(Literals const& l, size_t idx) { return config.literals_get(l,idx); }

    template<class IfVar, class IfOne, class IfMul, class IfAdd, class IfFloor>
    auto matchTerm(Term t, 
        IfVar   if_var, 
        IfOne   if_one, 
        IfMul   if_mul, 
        IfAdd   if_add, 
        IfFloor if_floor) -> decltype(if_one()) {
      return config.matchTerm(t,if_var,if_one,if_mul,if_add,if_floor);
    }
  };
 

  template<class Config>
  auto simplifyingConfig(Config c)
  { return SimplifyingConfig<Config>(std::move(c)); }

  using namespace sugar;

  template<class Config
    , bool optimizeBounds = true
    , bool optimizeGridIntersection = false
    >
  class Viras {

    template<class Conf>
    friend class VirasTest;

    using Numeral  = sugar::Numeral<Config>;
    using Term     = sugar::Term<Config>;
    using Literals = sugar::Literals<Config>;
    using Literal  = sugar::Literal<Config>;
    using Var      = sugar::Var<Config>;

    Config _config;
  public:

    Viras(Config c) : _config(std::move(c)) { };

    ~Viras() {};

    struct Break {
      Term t;
      Numeral p;
      Break(Term t, Numeral p) : t(t), p(p) { VIRAS_ASSERT(p > 0) }
      friend std::ostream& operator<<(std::ostream& out, Break const& self)
      { return out << self.t << " + " << self.p << "ℤ"; }
      DERIVE_TUPLE(Break,t,p)
      DERIVE_TUPLE_EQ
    };

    template<class L, class R> struct Add { L l; R r; };
    template<class L, class R> struct Mul { L l; R r; };

    template<class L, class R>
    Term eval(Add<L, R> x) { return _config.add(eval(x.l), eval(x.r)); };

    template<class T>
    struct Expr : public std::variant<T> { };

    friend Term grid_ceil (Term t, Break s_pZ) { return t + rem(s_pZ.t - t, s_pZ.p); }
    friend Term grid_floor(Term t, Break s_pZ) { return t - rem(t - s_pZ.t, s_pZ.p); }

    struct LiraTerm {
      Term self;
      Var x;
      Term lim;
      Numeral sslp;
      Numeral oslp;
      Numeral per;
      Numeral deltaY;
      Term distYminus;
      Term distYplus() { return distYminus + deltaY; }
      std::vector<Break> breaks;
      Term distXminus() const {
        return -(1 / oslp) * (oslp > 0 ? distYminus + deltaY
                                       : distYminus         );
      }
      Term distXplus() const { 
        using namespace sugar;
        return  -(1 / oslp) * (oslp > 0 ? distYminus
                                        : distYminus + deltaY);

      }
      Numeral deltaX() const { return abs(1/oslp) * deltaY; }
      Term lim_at(Term x0) const { return subs(lim, x, x0); }
      Term dseg(Term x0) const { return -(sslp * x0) + lim_at(x0); }
      Term zero(Term x0) const { return x0 - lim_at(x0) / sslp; }
      bool periodic() const { return oslp == 0; }
      friend std::ostream& operator<<(std::ostream& out, LiraTerm const& self)
      { return out << self.self; }
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
    static constexpr Infty infty { .positive = true, };


    struct ZComp {
      Numeral period;

      explicit ZComp(Numeral period) : period(period) {}

      friend std::ostream& operator<<(std::ostream& out, ZComp const& self)
      { return out << self.period << "ℤ"; }
      DERIVE_TUPLE(ZComp, period)
      DERIVE_TUPLE_EQ
      DERIVE_TUPLE_LESS
    };

    ZComp Z(Numeral n) { return ZComp(n); }
    ZComp Z(int n) { return ZComp(numeral(n)); }
    ZComp Z(int n, int m) { return ZComp(numeral(n) / m); }

    struct LiraLiteral {
      LiraTerm term;
      PredSymbol symbol;

      bool lim_pos_inf() const { return lim_inf(/* pos */ true); }
      bool lim_neg_inf() const { return lim_inf(/* pos */ false); }
      bool periodic() const { return term.periodic(); }

      bool lim_inf(bool positive) const
      { 
        VIRAS_ASSERT(term.oslp != 0);
        switch (symbol) {
        case PredSymbol::Gt:
        case PredSymbol::Geq: return positive ? term.oslp > 0 
                                              : term.oslp < 0;
        case PredSymbol::Neq: return true;
        case PredSymbol::Eq: return false;
        }
      }

      bool lim(Infty i) const
      { return lim_inf(i.positive); }

      friend std::ostream& operator<<(std::ostream& out, LiraLiteral const& self)
      { return out << self.term << " " << self.symbol << " 0"; }
    };

    Numeral numeral(int i)  { return Numeral { &_config, _config.numeral(i)}; }
    Term    term(Numeral n) { return Term    { &_config, _config.term(n.inner) }; }
    Term    term(Var v)     { return Term    { &_config, _config.term(v.inner) }; }
    Term    term(int i)     { return term(numeral(i)); }

    Var test_var(const char* name) { return Var { &_config, _config.test_var(name) }; }

    enum class Bound {
      Open,
      Closed,
    };

    auto intersectGrid(Break s_pZ, Bound l, Term t, Numeral k, Bound r) {
      auto p = s_pZ.p;
      auto start = [&]() {
        switch(l) {
          case Bound::Open:   return grid_floor(t + p, s_pZ);
          case Bound::Closed: return grid_ceil(t, s_pZ);
        };
      }();
      VIRAS_ASSERT(k != 0 || (l == Bound::Closed && r == Bound::Closed));
      return iter::if_then_(optimizeGridIntersection && k == 0, iter::vals(start))
                   else____(iter::nat_iter(numeral(0))
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

    // TODO get rid of implicit copies of LiraTerm
    // TODO make it possible to fail gracefully with uniterpreted stuff

    template<class MatchRec>
    Term calcLim(LiraTerm const& self, Var const& x, MatchRec matchRec) {
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
    Numeral calcPer(LiraTerm const& self, Var const& x, MatchRec matchRec) {
       return matchRec(
        /* var y */ [&](auto y) 
        { return numeral(0); },

        /* numeral 1 */ [&]() 
        { return numeral(0); },

        /* k * t */ [&](auto k, auto t, auto& rec) 
        { return rec.per; },

        /* l + r */ [&](auto l, auto r, auto& rec_l, auto& rec_r) 
        { return rec_l.per == 0 ? rec_r.per
               : rec_r.per == 0 ? rec_l.per
               : lcm(rec_l.per, rec_r.per); },

        /* floor t */   [&](auto t, auto& rec) 
        { return rec.per == 0 && rec.oslp == 0 ? numeral(0)
               : rec.per == 0                  ? 1 / abs(rec.oslp)
               : num(rec.per) * den(rec.oslp); }
        );
    }

    template<class MatchRec>
    Numeral calcSslp(LiraTerm const& self, Var const& x, MatchRec matchRec) {
       return matchRec(
        /* var y */ [&](auto y) 
        { return numeral(y == x ? 1 : 0); }

        /* numeral 1 */ , [&]() 
        { return numeral(0); }

        /* k * t */ , [&](auto k, auto t, auto& rec) 
        { return k * rec.sslp; }

        /* l + r */ , [&](auto l, auto r, auto& rec_l, auto& rec_r) 
        { return rec_l.sslp + rec_r.sslp; }

        /* floor t */ , [&](auto t, auto& rec) 
        { return numeral(0); }
        );
    }


    template<class MatchRec>
    Numeral calcOslp(LiraTerm const& self, Var const& x, MatchRec matchRec) {
       return matchRec(
        /* var y */ [&](auto y) 
        { return numeral(y == x ? 1 : 0); }

        /* numeral 1 */ , [&]() 
        { return numeral(0); }

        /* k * t */ , [&](auto k, auto t, auto& rec) 
        { return k * rec.oslp; }

        /* l + r */ , [&](auto l, auto r, auto& rec_l, auto& rec_r) 
        { return rec_l.oslp + rec_r.oslp; }

        /* floor t */ , [&](auto t, auto& rec) 
        { return rec.oslp; }
        );
    }


    template<class MatchRec>
    Numeral calcDeltaY(LiraTerm const& self, Var const& x, MatchRec matchRec) {
       return matchRec(
        /* var y */ [&](auto y) 
        { return numeral(0); }

        /* numeral 1 */ , [&]() 
        { return numeral(0); }

        /* k * t */ , [&](auto k, auto t, auto& rec) 
        { return abs(k) * rec.deltaY; }

        /* l + r */ , [&](auto l, auto r, auto& rec_l, auto& rec_r) 
        { return rec_l.deltaY + rec_r.deltaY; }

        /* floor t */ , [&](auto t, auto& rec)  {
          VIRAS_ASSERT(self.per != 0 || rec.per == 0);
          return optimizeBounds 
               ? (self.per == 0 ? numeral(0) : rec.deltaY + 1)
               :                               rec.deltaY + 1 ; 
        }
        );
    }


    template<class MatchRec>
    Term calcDistYminus(LiraTerm const& self, Var const& x, MatchRec matchRec) {
       return matchRec(
        /* var y */ [&](auto y) 
        { return y == x ? term(0) : term(y); }

        /* numeral 1 */ , [&]() 
        { return term(numeral(1)); }

        /* k * t */ , [&](auto k, auto t, auto& rec) 
        { return k >= 0 ? k * rec.distYminus : k * rec.distYplus(); }

        /* l + r */ , [&](auto l, auto r, auto& rec_l, auto& rec_r) 
        { return rec_l.distYminus + rec_r.distYminus; }

        /* floor t */ , [&](auto t, auto& rec) 
        { 
          VIRAS_ASSERT(self.per != 0 || rec.per == 0);
          return optimizeBounds 
               ? (self.per == 0 ? floor(rec.distYminus) :  rec.distYminus - 1)
               :                                           rec.distYminus - 1 ; }
        );
    }


    template<class MatchRec>
    std::vector<Break> calcBreaks(LiraTerm const& self, Var const& x, MatchRec matchRec) {
       return matchRec(
        /* var y */ [&](auto y) 
        { return std::vector<Break>(); }

        /* numeral 1 */ , [&]() 
        { return std::vector<Break>(); }

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
            return std::vector<Break>{Break(rec.zero(term(0)), self.per)};
          } else {
            auto p_min = *(iter::array(rec.breaks) 
              | iter::map([](auto b) -> Numeral { return b->p; })
              | iter::min);
            auto breaks = std::vector<Break>();
            for ( auto b0p_pZ : rec.breaks ) {
              auto b0p = b0p_pZ.t;
              auto p   = b0p_pZ.p;
              intersectGrid(b0p_pZ, 
                            Bound::Closed, b0p, self.per, Bound::Open) 
                | iter::foreach([&](auto b0) {
                    intersectGrid(Break(rec.zero(b0), 1/abs(rec.sslp)), 
                                  Bound::Closed, b0, p_min, Bound::Open)
                      | iter::foreach([&](auto b) {
                          breaks.push_back(Break(b, self.per));
                      });
                });
            }
            breaks.insert(breaks.end(), rec.breaks.begin(), rec.breaks.end());
            return breaks;
          }
        }
        );
    }

    LiraTerm analyse(Term self, Var x) {
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

        if (optimizeBounds) {
          VIRAS_ASSERT(res.per != 0 || res.deltaY == 0);
        }
        VIRAS_ASSERT((res.per == 0) == (res.breaks.size() == 0));
        return res;
    }

    LiraLiteral analyse(Literal self, Var x) 
    { return LiraLiteral { analyse(self.term(), x), self.symbol() }; }

    std::vector<LiraLiteral> analyse(Literals const& self, Var x) 
    { 
      std::vector<LiraLiteral> out;
      iter::array(self) 
        | iter::map([&](auto lit) { return analyse(lit, x); })
        | iter::foreach([&](auto lit) { return out.push_back(std::move(lit)); });
      return out; 
    }


    std::vector<LiraLiteral> analyse(typename Config::Literals const& self, typename Config::Var x) 
    { return analyse(Literals { &_config, self }, Var { &_config, x }); }

    struct Epsilon {
      friend std::ostream& operator<<(std::ostream& out, Epsilon const& self)
      { return out << "ε"; }
      DERIVE_TUPLE(Epsilon,)
      DERIVE_TUPLE_EQ
      DERIVE_TUPLE_LESS
    };
    static constexpr Epsilon epsilon;

    struct VirtualTerm {
      std::optional<Term> term;
      std::optional<Epsilon> epsilon;
      std::optional<Numeral> period;
      std::optional<Infty> infty;
    public:
      VirtualTerm(
        std::optional<Term> term,
        std::optional<Epsilon> epsilon,
        std::optional<Numeral> period,
        std::optional<Infty> infinity) 
        : term(std::move(term))
        , epsilon(std::move(epsilon))
        , period(std::move(period))
        , infty(std::move(infinity))
      {
        VIRAS_ASSERT(term || infinity);
        VIRAS_ASSERT(!infty || !period);
      }

      VirtualTerm(Numeral n) : VirtualTerm(to_term(n)) {}
      VirtualTerm(Break t_pZ) : VirtualTerm(std::move(t_pZ.t), {}, std::move(t_pZ.p), {}) {}
      VirtualTerm(Infty infty) : VirtualTerm({}, {}, {}, infty) {}
      VirtualTerm(Term t) : VirtualTerm(std::move(t), {}, {}, {}) {}

      friend VirtualTerm operator+(VirtualTerm const& t, Epsilon const);

      static VirtualTerm periodic(Term b, Numeral p) { return VirtualTerm(std::move(b), {}, std::move(p), {}); }

      friend std::ostream& operator<<(std::ostream& out, VirtualTerm const& self)
      { 
        bool fst = true;
#define __OUTPUT(field)                                                                   \
        if (fst) { out << field; fst = false; }                                           \
        else { out << " + " << field; }                                                   \

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




    friend VirtualTerm operator+(Term const& t, Epsilon const) 
    { return VirtualTerm(t) + epsilon; }

    friend VirtualTerm operator+(VirtualTerm const& t, Epsilon const) 
    { 
      VirtualTerm out = t;
      out.epsilon = std::optional<Epsilon>(epsilon);
      return out; 
    }

    friend VirtualTerm operator+(Numeral const& t, Epsilon const) 
    { return to_term(t) + epsilon; }


    friend VirtualTerm operator+(Term const& t, ZComp const& z) 
    { return VirtualTerm(t) + z; }

    friend VirtualTerm operator+(Numeral const& t, ZComp const& z) 
    { return to_term(t) + z; }

    friend VirtualTerm operator+(int t, ZComp const& z) 
    { return to_numeral(z.period.config, t) + z; }

    friend VirtualTerm operator+(VirtualTerm const& t, ZComp const& z) 
    { 
      VirtualTerm out = t;
      out.period = std::optional<Numeral>(z.period);
      return out; 
    }

    friend VirtualTerm operator+(Term const& t, Infty const& i) 
    { return VirtualTerm(t) + i; }

    friend VirtualTerm operator+(VirtualTerm const& t, Infty const& i) 
    { 
      VirtualTerm out = t;
      out.infty = std::optional<Infty>(i);
      return out; 
    }

    friend VirtualTerm operator+(Numeral const& t, Infty const& i) 
    { return to_term(t) + i; }

    auto elim_set(Var x, LiraLiteral const& lit)
    {
      auto& t = lit.term;
      auto symbol = lit.symbol;
      auto isIneq = [](auto symbol) { return (symbol == PredSymbol::Geq || symbol == PredSymbol::Gt); };
      using VT = VirtualTerm;

      return iter::if_then_(t.breaks.empty(), 
                           iter::if_then_(t.sslp == 0              , iter::vals<VT>(-infty))
                                 else_if_(symbol == PredSymbol::Neq, iter::vals<VT>(-infty, t.zero(term(0)) + epsilon))
                                 else_if_(symbol == PredSymbol:: Eq, iter::vals<VT>(t.zero(term(0))))
                                 else_if_(t.sslp < 0               , iter::vals<VT>(-infty))
                                 else_if_(symbol == PredSymbol::Geq, iter::vals<VT>(t.zero(term(0))))
                                 else_is_(symbol == PredSymbol::Gt , iter::vals<VT>(t.zero(term(0)) + epsilon))
                                 | iter_dbg(1, "lra term")
                                 )

                   else_is_(!t.breaks.empty(), [&]() { 
                       auto ebreak       = [&]() {
                       return 
                         iter::if_then_(t.periodic(), 
                                        iter::array(t.breaks) 
                                          | iter::map([&](auto* b) { return VT(*b); }) )

                               else____(iter::array(t.breaks) 
                                          | iter::flat_map([&](auto* b) { return intersectGrid(*b, Bound::Open, t.distXminus(), t.deltaX(), Bound::Open); })
                                          | iter::map([](auto t) { return VT(t); }) )
                       | iter_dbg(1, "ebreak")
                       ; };

                       auto breaks_plus_epsilon = [&]() { return ebreak() | iter::map([](auto vt) { return vt + epsilon; })
                       ; };

                       auto ezero = [&]() { 
                       return 
                          iter::if_then_(t.periodic(), 
                                         iter::array(t.breaks) 
                                           | iter::map([&](auto* b) { return VT::periodic(t.zero(b->t), b->p); }))

                                else_if_(t.oslp == t.sslp,
                                         iter::array(t.breaks) 
                                           | iter::map([&](auto* b) { return VT(t.zero(b->t)); }))

                                else____(iter::array(t.breaks) 
                                           | iter::flat_map([&](auto* b) { return intersectGrid(Break(t.zero(b->t), 1 - t.oslp / t.sslp),
                                                                                                Bound::Open, t.distXminus(), t.deltaX(), Bound::Open); })
                                           | iter::map([&](auto t) { return VT(t); }))
                                         
                                 | iter_dbg(1, "ezero")
                       ; };
                       auto eseg         = [&]() { 
                         return 
                           iter::if_then_(t.sslp == 0 || ( t.sslp < 0 && isIneq(symbol)), breaks_plus_epsilon())
                                 else_if_(t.sslp >  0 && symbol == PredSymbol::Geq, iter::concat(breaks_plus_epsilon(), ezero()))
                                 else_if_(t.sslp >  0 && symbol == PredSymbol::Gt , iter::concat(breaks_plus_epsilon(), ezero() | iter::map([](auto x) { return x + epsilon; })))
                                 else_if_(t.sslp != 0 && symbol == PredSymbol::Neq, iter::concat(breaks_plus_epsilon(), ezero() | iter::map([](auto x) { return x + epsilon; })))
                                 else_is_(t.sslp != 0 && symbol == PredSymbol::Eq,  ezero())
                                 | iter_dbg(1, "eseg")
                       ; };
                       auto ebound_plus  = [&]() { return 
                           iter::if_then_(lit.lim_pos_inf(), iter::vals<VT>(t.distXplus(), t.distXplus() + epsilon))
                                 else____(                   iter::vals<VT>(t.distXplus()                         ))
                                 | iter_dbg(1, "ebound_plus")
                                 ; };

                       auto ebound_minus = [&]() { return 
                           iter::if_then_(lit.lim_neg_inf(), iter::vals<VT>(t.distXminus(), -infty))
                                 else____(                   iter::vals<VT>(t.distXminus()        ))
                                 | iter_dbg(1, "ebound_minus")
                       ; };

                       return iter::if_then_(t.periodic(), iter::concat(ebreak(), eseg()))
                                    else____(              iter::concat(ebreak(), eseg(), ebound_plus(), ebound_minus()));
                   }());

    }

    auto elim_set(Var x, std::vector<LiraLiteral> const& lits)
    { return iter::array(lits)
        | iter::flat_map([&](auto lit) { return elim_set(x, *lit); }); }

    Literal literal(Term t, PredSymbol s) 
    { return Literal { &_config, _config.create_literal(t.inner, s), }; }

    Literal literal(bool b) { return literal(term(0), b ? PredSymbol::Eq : PredSymbol::Neq); }

    Literal vsubs_aperiodic0(LiraLiteral const& lit, Var x, VirtualTerm vt) {
      auto impl = [&]() {

      auto& s = lit.term;
      auto symbol = lit.symbol;
      VIRAS_ASSERT(!vt.period);
      if (vt.infty) {
        /* case 3 */
        if (s.periodic()) {
          vt.infty = {};
          if (!vt.term) {
            vt.term = term(0);
          }
          return vsubs_aperiodic0(lit, x, vt);
        } else {
          return literal(lit.lim_inf(vt.infty->positive));
        }
      } else if (vt.epsilon) {
        switch(symbol) {
          case PredSymbol::Eq:
          case PredSymbol::Neq: {
            /* case 4 */
            if (s.sslp != 0) {
              return symbol == PredSymbol::Eq ? literal(false) : literal(true);
            } else {
              return literal(s.lim_at(*vt.term), symbol);
            }
          }
          case PredSymbol::Geq:
          case PredSymbol::Gt: {
            /* case 5 */
            return literal(s.lim_at(*vt.term), 
                  s.sslp > 0 ? PredSymbol::Geq
                : s.sslp < 0 ? PredSymbol::Gt
                :              symbol);
          }
        }
      } else {
        VIRAS_ASSERT(!vt.epsilon && !vt.infty && !vt.period);
        return literal(subs(s.self, x, *vt.term), symbol);
      }
      };
      auto res = impl();
      VIRAS_LOG(1, "substituting ", lit, "[ ", x, " // ", vt, " ] = ", res)
      return res;
    }


    auto vsubs_aperiodic1(std::vector<LiraLiteral> const& lits, Var x, VirtualTerm term) {
      VIRAS_ASSERT(!term.period);
          /* case 2 */
      return iter::array(lits) 
        | iter::map([this, x, term](auto lit) { return vsubs_aperiodic0(*lit, x, term); });
    }

    auto vsubs(std::vector<LiraLiteral> const& lits, Var x, VirtualTerm vt) {
      return iter::if_then_(vt.period, ([&](){
                              /* case 1 */
                              auto A = [&lits]() { return iter::array(lits) | iter::filter([](auto l) { return !l->periodic(); }); };
                              auto P = [&lits]() { return iter::array(lits) | iter::filter([](auto l) { return l->periodic(); }); };

                              VIRAS_ASSERT((P() | iter::count()) > 0); // if there are no periodic literals we cannot have periodic solution terms
                              Numeral lambda = *(P()
                                             | iter::map([&](auto L) { return L->term.per; })
                                             | iter::fold([](auto l, auto r) { return lcm(l, r); }));

                              auto iGrid = [this, vt](auto... args) { 
                              return intersectGrid(Break(*vt.term, *vt.period), args...)
                                                  | iter::map([](auto x) { return VirtualTerm(x); });
                              ; };
                              auto all_lim_top = [A](Infty inf) { return A() | iter::all([inf](auto l) { return l->lim(inf) == true; }); };
                              auto one_lambda_plus = [iGrid, vt, lambda](Infty inf) {
                                return iGrid(Bound::Closed, *vt.term, lambda, Bound::Open) 
                                     | iter::map([&](auto s) { return s + inf; });
                              };
                              std::optional<LiraLiteral const*> aperiodic_equality;
                              auto aperiodic_equality_exists = [&]() -> bool { 
                                aperiodic_equality = A()
                                                   | iter::filter([](auto l) { return l->symbol == PredSymbol::Eq; })
                                                   | iter::min_by_key([](auto l) { return l->term.deltaX(); });
                                return bool(aperiodic_equality);
                              };
                              auto fin = 
                                iter::if_then_(all_lim_top( infty), one_lambda_plus( infty))
                                      else_if_(all_lim_top(-infty), one_lambda_plus(-infty))
                                      else_if_(aperiodic_equality_exists(), 
                                               iGrid(Bound::Closed, (**aperiodic_equality).term.distXminus(), (**aperiodic_equality).term.deltaX(), Bound::Closed))
                                      else____(
                                            A()
                                          | iter::filter([&](auto L) { return L->lim(-infty) == false; })
                                          | iter::flat_map([lambda, iGrid](auto L) { return iGrid(Bound::Closed, L->term.distXminus(), L->term.deltaX() + lambda, Bound::Closed); })
                                          )
                                         | iter_dbg(1, "fin");
                              return std::move(fin) 
                              | iter::map([this,&lits,x](auto t) { return vsubs_aperiodic1(lits, x, t); });
                            }()))
                   else____( ([&]() {
                         auto out = iter::vals(vsubs_aperiodic1(lits, x, vt));
                         return out;
                       }()));
    }

    auto quantifier_elimination(Var x, std::vector<LiraLiteral> const& lits)
    {
      return elim_set(x, lits)
        | iter::dedup()
        | iter_dbg(0, "elim set: ")
        | iter::flat_map([this,&lits,x](auto t) { return vsubs(lits, x, t); });
    }

    auto quantifier_elimination(typename Config::Var x, Literals const& ls)
    {
      auto lits = std::make_unique<std::vector<LiraLiteral>>(analyse(ls, x));
      return quantifier_elimination(Var { &_config, x }, *lits)
        | iter::inspect([ /* we store the pointer to the literals in this closure */ lits = std::move(lits)](auto) { })
        | iter::map([&](auto lits) { return std::move(lits) | iter::map([](auto lit) { return lit.inner; }); });
    }

    auto quantifier_elimination(typename Config::Var x, std::vector<LiraLiteral> const& lits)
    {
      return quantifier_elimination(Var { &_config, x }, lits)
        | iter::map([&](auto lits) { return std::move(lits) | iter::map([](auto lit) { return lit.inner; }); });
    }

  };

  template<class Config>
  auto viras(Config c) { return Viras<Config>(std::move(c)); }


}
