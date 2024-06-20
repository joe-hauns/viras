#pragma once
#include "viras/config_macros.h"

#include "viras/output.h"
#include "viras/iter.h"
#include "viras/derive.h"
#include "viras/predicate.h"
#include "viras/sugar.h"
#include "viras/virtual_term.h"
#include "viras/lira_term.h"
#include "viras/break.h"

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
    static constexpr bool optimizeBounds = Config::optimizeBounds;
    static constexpr bool optimizeGridIntersection = Config::optimizeGridIntersection;

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
    using Break    = viras::Break<Config>;
    using Epsilon = viras::Epsilon;
    using VirtualTerm = viras::VirtualTerm<Config>;
    using Infty = viras::Infty;
    using ZComp = viras::ZComp<Config>;
    using LiraTerm = viras::LiraTerm<Config>;

    Config _config;
  public:

    Viras(Config c) : _config(std::move(c)) { };

    ~Viras() {};

    static constexpr Infty infty { .positive = true, };


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

    // TODO get rid of implicit copies of LiraTerm
    // TODO make it possible to fail gracefully with uniterpreted stuff
    // TODO get rid of this?
    static LiraTerm analyse(Term self, Var x) { return LiraTerm::analyse(self,x); }

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

    static constexpr Epsilon epsilon;

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

                              auto iGrid = [ vt](auto... args) { 
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
