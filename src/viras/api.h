#pragma once
#include <utility>
#include <map>
#include "viras/predicate.h"
#include "viras/iter.h"

namespace viras {

  struct DefaultOpts 
  {
    static bool constexpr optimizeBounds() { return true; }
    static bool constexpr optimizeGridIntersection() { return false; }
    static bool constexpr simplify() { return true; }
  };

  template<class A, class O>
  struct Config
  {
    using Api = A;
    using Opts = O;

    Api api;
    Opts opts;

    Config(Api api, Opts opts) 
      : api(std::move(api))
      , opts(std::move(opts)) {}

    /* types that must be defined by Api */
    using Literals = typename Api::Literals;
    using Literal  = typename Api::Literal;
    using Var      = typename Api::Var;
    using Term     = typename Api::Term;
    using Numeral  = typename Api::Numeral;

    /* direct api calls */
    Numeral numeral(int i) { return api.numeral(i); }
    Numeral lcm(Numeral l, Numeral r) { return api.lcm(l, r); }
    Numeral gcd(Numeral l, Numeral r) { return api.gcd(l, r); }
    Numeral mul(Numeral l, Numeral r) { return api.mul(l,r); }
    Numeral add(Numeral l, Numeral r) { return api.add(l,r); }
    Numeral floor(Numeral t)          { return api.floor(t); }
    Numeral inverse(Numeral n)        { return api.inverse(n); }
    bool less(Numeral l, Numeral r)   { return api.less(l,r); }
    bool leq(Numeral l, Numeral r)    { return api.leq(l,r); }
    Numeral num(Numeral l)            { return api.num(l); }
    Numeral den(Numeral l)            { return api.den(l); }

    void output(std::ostream& out, Literals const& x) { api.output(out, x); }
    // TODO fix this
    // void output(std::ostream& out, Literal const& x)  { api.output(out, x); }
    void output(std::ostream& out, Var const& x)      { api.output(out, x); }
    void output(std::ostream& out, Term const& x)     { api.output(out, x); }
    void output(std::ostream& out, Numeral const& x)  { api.output(out, x); }

    Term term(Numeral n)                                { return api.term(n); }
    Term term(Var v)                                    { return api.term(v); }

    /* only used in VirasTest. doesn't have to be defiend otherwise */
    Var test_var(const char* name)                      { return api.test_var(name); }

    PredSymbol symbol_of_literal(Literal l)             { return api.symbol_of_literal(l); }
    Term term_of_literal(Literal l)                     { return api.term_of_literal(l); }
    Literal create_literal(Term t, PredSymbol s)        { return api.create_literal(t,s); }

    size_t literals_size(Literals const& l)             { return api.literals_size(l); }
    Literal literals_get(Literals const& l, size_t idx) { return api.literals_get(l,idx); }

    template<class IfVar, class IfOne, class IfMul, class IfAdd, class IfFloor>
    auto matchTerm(Term t, 
        IfVar   if_var, 
        IfOne   if_one, 
        IfMul   if_mul, 
        IfAdd   if_add, 
        IfFloor if_floor) -> decltype(if_one()) {
      return api.matchTerm(t,if_var,if_one,if_mul,if_add,if_floor);
    }

    /* simplifying api calls */
    Term mul(Numeral l, Term r) {
      if (!opts.simplify()) { return api.mul(l,r); }
      auto dflt = [&](auto...) { return api.mul(l,r); };
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

    Term add(Term l, Term r) { 
      if (!opts.simplify()) { return api.add(l,r); }
      std::map<Term, Numeral> summands;
      auto addUp = [&](auto t) {
        for_monom(t, [&](Numeral n, Term t) {
            auto res_iter = summands.insert(std::make_pair(t, numeral(0))).first;
            auto& res = (*res_iter).second;
            res = api.add(res, n);
        });
      };
      addUp(l);
      addUp(r);

      return iterToSum(iter::stl(summands));
    }

    Term floor(Term t) { 
      if (!opts.simplify()) { return api.floor(t); }
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
            update(outer, r, [&](auto i)  { return i +      api.floor(l) ; });
            update(inner, r, [&](auto i) { return i + (l - api.floor(l)); });
          } else {
            update(inner, r, [&](auto i) { return i + l; });
          }
      });

      auto in_t = iterToSum(iter::stl(inner));
      auto num = tryNumeral(in_t);
      if (num) {
        auto fnum = api.floor(*num);
        if (fnum != numeral(0)) {
          update(outer, term(numeral(1)), [&](auto n) { return n + fnum; });
        }
      } else {
        update(outer, api.floor(in_t), [&](auto n) { return n + numeral(1); });
      }
      return iterToSum(iter::stl(outer));
    }

    /* helper functions */

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
        | iter::fold([this](auto l, auto r) { return api.add(l, r); });
      return res ? *res : api.term(api.numeral(0));
    }


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


  };

} // namespace viras
