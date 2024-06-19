#pragma once

#include <optional>
#include <iostream>
#include <set>
#include <map>
#include <tuple>

#ifndef VIRAS_ASSERT
#include <cassert>
#define VIRAS_ASSERT(...) assert(__VA_ARGS__);
#endif // VIRAS_ASSERT

#define VIRAS_LOG(...) std::cout << __VA_ARGS__ << std::endl;

#define DERIVE_TUPLE(Slf,...)                                                             \
      using Self = Slf;                                                                   \
      auto asTuple() const { return std::tie(__VA_ARGS__); }                              \

#define DERIVE_TUPLE_EQ                                                                   \
      friend bool operator==(Self const& lhs, Self const& rhs)                            \
      { return lhs.asTuple() == rhs.asTuple(); }                                          \

#define DERIVE_TUPLE_LESS                                                                 \
      friend bool operator<(Self const& lhs, Self const& rhs)                             \
      { return lhs.asTuple() < rhs.asTuple(); }                                           \


namespace viras {

  template<class C>
  struct OutputPtr  { C const& self; };
  template<class C>
  OutputPtr<C> outputPtr(C const& c)  { return OutputPtr<C> { c }; }

  template<class C>
  std::ostream& operator<<(std::ostream& out, OutputPtr<C*> const& self)
  { return self.self == nullptr ? out << "nullptr" : out << *self.self; }

  template<class C>
  std::ostream& operator<<(std::ostream& out, OutputPtr<C> const& self)
  { return out << self.self; }


  template<class T>
  T dummyVal();

  namespace iter {

    template<class T> struct opt_value_type;
    template<template<class> class Tmplt, class T> struct opt_value_type<Tmplt<T>> { using type = T; };

    template<class I>
    // using value_type = typename opt_value_type<decltype(((I*)0)->next())>::type;
    using value_type = typename decltype(((I*)0)->next())::value_type;


    template<class Op>
    struct IterCombinator {
      Op self;
      template<class I>
      friend auto operator|(I iter, IterCombinator self) -> decltype(auto) 
      { return (self.self)(std::move(iter)); }

      template<class Op2>
      auto compose(IterCombinator<Op2> other) {
        return iterCombinator([self = std::move(this->self), other = std::move(other)](auto iter){ return (other.self)((self)(std::move(iter))); });
      }
    };

    template<class O>
    constexpr IterCombinator<O> iterCombinator(O o) 
    { return IterCombinator<O>{ std::move(o) }; }

    constexpr auto foreach = [](auto f) {
      return iterCombinator([f = std::move(f)](auto iter) {
        while (true) {
          auto x = iter.next();
          if (x) {
            f(*x);
          } else {
            break;
          }
        }
      });
    };


    constexpr auto collect_vec = 
      iterCombinator([](auto iter) {
        std::vector<value_type<decltype(iter)>> out;
        std::move(iter) | foreach([&](auto x) { out.push_back(std::move(x)); });
        return out;
      });

    template<class C = size_t>
    auto count() {
      return iterCombinator([](auto iter) {
          C out = 0;
          std::move(iter) | foreach([&](auto) { return out = out + 1; });
          return out;
      });
    }


    constexpr auto fold = [](auto f) {
      return iterCombinator([f = std::move(f)](auto iter) -> std::optional<decltype(f(*iter.next(), *iter.next()))> {
          auto fst = iter.next();
          if (fst) {
            auto res = *fst;
            for (auto x = iter.next(); x; x = iter.next()) {
              res = f(res, *x);
            }
            return res;
          } else {
            return {};
          }
      });
    };


    constexpr auto all = [](auto f) {
      return iterCombinator([f = std::move(f)](auto iter) {
          for (auto x = iter.next(); x; x = iter.next()) {
            if (!f(*x))
              return false;
          }
          return true;
      });
    };


    constexpr auto any = [](auto f) {
      return iterCombinator([f = std::move(f)](auto iter) {
          for (auto x = iter.next(); x; x = iter.next()) {
            if (f(*x))
              return true;
          }
          return false;
      });
    };

    constexpr auto find = [](auto f) {
      return iterCombinator([f = std::move(f)](auto iter) -> std::optional<value_type<decltype(iter)>> {
          using res = std::optional<value_type<decltype(iter)>>;
          for (auto x = iter.next(); x; x = iter.next()) {
            if (f(*x))
              return res(*x);
          }
          return res();
      });
    };

    template<class I, class F>
    struct MapIter {
      I i;
      F f;
      auto next() -> decltype(auto) { 
        auto next = i.next();
        return next ? std::optional<decltype(f(*next))>(f(*next))
                    : std::optional<decltype(f(*next))>();
      }
    };

    constexpr auto map = [](auto f) {
      return iterCombinator([f = std::move(f)](auto i) {
        return MapIter<decltype(i), decltype(f)>{std::move(i),std::move(f)};
      });
    };


    template<class I, class F>
    struct FilterIter {
      I i;
      F f;
      auto next() -> decltype(auto) { 
        auto e = i.next();
        while (e && !f(*e))
          e = i.next();
        return e;
      }
    };

    constexpr auto filter = [](auto f) {
      return iterCombinator([f = std::move(f)](auto i) {
        return FilterIter<decltype(i), decltype(f)>{std::move(i),std::move(f)};
      });
    };


    inline auto dedup() {
      return iterCombinator([](auto iter) {
            return std::move(iter)
              | filter([set = std::set<
                  value_type<decltype(iter)>
                  >()](auto e) mutable {
                  return set.insert(e).second;
              });
        });
    }

    template<class I, class F>
    struct TakeWhileIter {
      I i;
      F f;
      bool end;
      std::optional<value_type<I>> next() { 
        if (end) {
          return {};
        } else {
          auto e = i.next();
          if (!bool(e) || !f(*e)) {
            end = true;
            return {};
          } else {
            return std::optional<value_type<I>>(std::move(e));
          }
        }
      }
    };

    constexpr auto take_while = [](auto f) {
      return iterCombinator([f = std::move(f)](auto i) {
        return TakeWhileIter<decltype(i), decltype(f)>{ std::move(i),std::move(f), false, };
      });
    };

    template<class I>
    struct FlattenIter {
      I outer;
      std::optional<value_type<I>> inner;
      bool init;

      FlattenIter(I i): outer(std::move(i)), inner(), init(false) {}

      std::optional<value_type<value_type<I>>> next()
      {
        if (!init) {
          inner.~decltype(inner)();
          new(&inner) decltype(inner)(outer.next());
          init = true;
        }
        while (inner) {
          auto next = inner->next();
          if (next) 
            return next;
          else {
            inner.~decltype(inner)();
            new(&inner) decltype(inner)(outer.next());
          }
        }
        return {};
      }
    };

    constexpr auto flatten = iterCombinator([](auto i) {
      return FlattenIter<decltype(i)>(i);
    });

    constexpr auto min_by = [](auto less) {
      return iterCombinator([less = std::move(less)](auto iter) {
        using out = std::optional<value_type<decltype(iter)>>;
        auto min_ = iter.next();
        if (min_) {
          auto min = std::move(*min_);
          for (auto x = iter.next(); x; x = iter.next()) {
            if (less(*x, min)) {
              min = std::move(*x);
            }
          }
          return out(std::move(min));
        } else {
          return out();
        }
      });
    };

    constexpr auto min = min_by([](auto l, auto r) { return l < r; });

    constexpr auto min_by_key = [](auto f) {
      return min_by([f = std::move(f)](auto l, auto r) { return f(l) < f(r); });
    };

    template<class F>
    auto inspect(F f) {
      return map([f = std::move(f)](auto x) {
          f(x);
          return std::move(x);
      });
    }

    template<class M>
    auto dbg(M msg) {
      return inspect([msg = std::move(msg)](auto x) { VIRAS_LOG(msg << ": " << outputPtr(x)); });
    }

    constexpr auto flat_map = [](auto f) {
      return map(f).compose(flatten);
    };

    template<class T>
    struct RangeIter {
      T lower;
      T upper;

      std::optional<T> next()
      {
        if (lower < upper) return std::optional(lower++);
        else return {};
      }
    };


    template<class L, class U>
    RangeIter<U> range(L lower, U upper)
    { return RangeIter<U>{U(std::move(lower)), std::move(upper)}; }

    template<class Begin, class End>
    struct StlIter {
      Begin cur;
      End end;
      using val_t = std::remove_reference_t<decltype(*cur)>*;

      std::optional<val_t> next()
      {
        if (cur != end)  {
          std::optional<val_t> out(&*cur);
          cur++;
          return out;
        } else {
          return std::optional<val_t>();
        }
      }
    };


    template<class StlIterable>
    auto stl(StlIterable const& a)
    { return StlIter<decltype(a.begin()), decltype(a.end())> { a.begin(), a.end() }; }

    template<class StlIterable>
    auto stl(StlIterable& a)
    { return StlIter<decltype(a.begin()), decltype(a.end())> { a.begin(), a.end() }; }

    template<class Array, 
      std::enable_if_t<std::is_reference_v<decltype(dummyVal<Array>()[0])>, bool> = true
      > auto array(Array const& a)
    { return range(0, a.size()) | map([&](auto i) { return &a[i]; }); }

    template<class Array,
      std::enable_if_t<std::is_reference_v<decltype(dummyVal<Array>()[0])>, bool> = true
      > auto array(Array      & a)
    { return range(0, a.size()) | map([&](auto i) { return &a[i]; }); }


    template<class Array, 
      std::enable_if_t<!std::is_reference_v<decltype(dummyVal<Array>()[0])>, bool> = true
      > auto array(Array const& a)
    { return range(0, a.size()) | map([&](auto i) { return a[i]; }); }

    template<class Array,
      std::enable_if_t<!std::is_reference_v<decltype(dummyVal<Array>()[0])>, bool> = true
      > auto array(Array      & a)
    { return range(0, a.size()) | map([&](auto i) { return a[i]; }); }


    // template<class Array> auto array_ptr(Array const& a)
    // { return range(0, a.size()) | map([&](auto i) { return &a[i]; }); }
    //
    // template<class Array> auto array_ptr(Array      & a)
    // { return range(0, a.size()) | map([&](auto i) { return &a[i]; }); }

    template<class F>
    struct ClosureIter {
      F fn;

      auto next() -> std::invoke_result_t<F>
      { return fn(); }
    };

    template<class F>
    ClosureIter<F> closure(F fn)
    { return ClosureIter<F>{std::move(fn)}; }

    template<class A>
    struct DummyIter {
      auto next() -> std::optional<A>;
    };

    template<class A>
    constexpr auto dummy() 
    { return DummyIter<A>{}; }


    template<class A, unsigned N>
    struct ValsIter {
      A _vals[N];
      unsigned _cur;

      auto next() -> std::optional<A>
      { return _cur < N ? std::optional<A>(std::move(_vals[_cur++]))
                        : std::optional<A>(); }
    };

    template<class A>
    constexpr auto empty() 
    { return ValsIter<A, 0> { ._cur = 0, }; }

    template<class A, class... As>
    constexpr auto vals(A a, As... as) 
    { return ValsIter<A, std::tuple_size_v<std::tuple<A, As...>>>{ ._vals = {std::move(a), std::move(as)...}, ._cur = 0, }; }


    template<class... Is>
    struct IfThenElseIter {
      std::variant<Is...> self;

      auto next()
      { return std::visit([](auto&& x){ return x.next(); }, self); }
    };

    template<class Conds, class... Thens>
    struct IfThen {
      Conds _conds;
      std::tuple<Thens...> _thens;

      template<class Cond, class Then>
      auto else_if(Cond c, Then t) -> IfThen<decltype(std::tuple_cat(_conds, std::make_tuple(c))), Thens..., Then> {
        return IfThen<decltype(std::tuple_cat(_conds, std::make_tuple(c))), Thens..., Then> {
          ._conds = std::tuple_cat(std::move(_conds), std::make_tuple(std::move(c))),
          ._thens = std::tuple_cat(std::move(_thens), std::make_tuple(std::move(t))),
        };
      }

      template<unsigned i, unsigned sz> 
      struct __TryIfThen {
        template<class Out>
        static std::optional<Out> apply(IfThen& self) {
          if (std::get<i>(self._conds)()) {
            auto then = std::get<i>(self._thens)();
            return std::optional<Out>(Out(std::in_place_index_t<i>(), std::move(then)));
          } else {
            return __TryIfThen<i + 1, sz>::template apply<Out>(self);
          }
        };
      };

      template<unsigned sz>
      struct __TryIfThen<sz, sz> {
        template<class Out>
        static std::optional<Out> apply(IfThen& self) {
          return {};
        };
      };

      template<class Else>
      auto else_(Else e) -> IfThenElseIter<
                         std::invoke_result_t<Thens>..., 
                         std::invoke_result_t<Else>> 
      {
        using Out = IfThenElseIter<std::invoke_result_t<Thens>..., 
                                  std::invoke_result_t<Else>>;
        using Var = std::variant<std::invoke_result_t<Thens>..., 
                                 std::invoke_result_t<Else>>;
        auto var = __TryIfThen<0, std::tuple_size_v<Conds>>::template apply<Var>(*this);
        if (var) {
          return Out{.self = std::move(*var)};
        } else {
          return Out{.self = Var(std::in_place_index_t<std::tuple_size_v<Conds>>(),e())};
        }
      }
    };

    template<class Cond, class Then>
    auto if_then(Cond c, Then t)
    { return IfThen<std::tuple<Cond>,Then> { std::make_tuple(std::move(c)), t }; }

#define if_then_(x, y) if_then([&]() { return x; }, [&]() { return y; }) 
#define else_if_(x, y) .else_if([&]() { return x; }, [&]() { return y; })
#define else____(x) .else_([&]() { return x; })
#define else_is_(x,y) .else_([&]() { VIRAS_ASSERT(x); return y; })


    template<class I, class... Is>
    struct ConcatIter {

      std::tuple<I, Is...> self;
      unsigned idx;

      template<unsigned i, unsigned sz> 
      struct __TryConcat {
        static std::optional<value_type<I>> apply(ConcatIter& self) {
          if (self.idx == i) {
            auto out = std::get<i>(self.self).next();
            if (out) {
              return out;
            } else {
              self.idx++;
            }
          }
          return __TryConcat<i + 1, sz>::apply(self);
        }
      };

      template<unsigned sz>
      struct __TryConcat<sz, sz> {
        static std::optional<value_type<I>> apply(ConcatIter& self) {
          return {};
        };
      };

      std::optional<value_type<I>> next()
      { return __TryConcat<0, std::tuple_size_v<std::tuple<I, Is...>>>::apply(*this); }
    };

    template<class... Is>
    ConcatIter<Is...> concat(Is... is) 
    { return ConcatIter<Is...> { std::make_tuple(std::move(is)...) }; }

    template<class T>
    struct NatIter {
      T _cur;

      std::optional<T> next() {
        auto out = _cur;
        _cur = _cur + 1;
        return out;
      }
    };


    template<class T>
    NatIter<T> nat_iter(T first = T(0)) {
      return NatIter<T> { ._cur = std::move(first) };
    }
  } // namespace iter

  enum class PredSymbol { Gt, Geq, Neq, Eq, };

  inline std::ostream& operator<<(std::ostream& out, PredSymbol const& self)
  { 
    switch(self) {
      case PredSymbol::Gt: return out << ">";
      case PredSymbol::Geq: return out << ">=";
      case PredSymbol::Neq: return out << "=";
      case PredSymbol::Eq: return out << "!=";
    }
  }



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
    } // TODO


    
    // typename Viras<Config>::VirtualTerm simpl(typename Viras<Config>::VirtualTerm self);

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

    // template<class F>
    // auto for_monom2(Term self, F f) {
    //   auto dflt = [&](auto...args){ f(numeral(1), self); return std::make_tuple(); };
    //   matchTerm(self, 
    //     /* var v */ dflt, 
    //
    //     /* numeral 1 */ dflt,
    //     /* k * t */ [&](auto k, auto t) { 
    //       f(k, t);  
    //       return std::make_tuple(); 
    //     }, 
    //     // /* k * t */ [&](auto k, auto t) { f(k, t);  return std::make_tuple(); }, 
    //
    //     /* l + r */ [&](auto l, auto r) { 
    //       for_monom2(l, f);
    //       for_monom2(r, f);
    //       return std::make_tuple();
    //     }, 
    //
    //     /* floor */ dflt
    //     );
    // }




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


      // auto numL = tryNumeral(l);
      // auto numR = tryNumeral(r);
      //
      // return isZero(l) ? r 
      //      : isZero(r) ? l
      //      : numL && numR ? term(config.add(*numL, *numR))
      //      : config.add(l,r); 
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

      // auto tNum = tryNumeral(t);
      // return tNum ? term(floor(*tNum)) : config.floor(t); 
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


  template<class Config
    , bool optimizeBounds = true
    , bool optimizeGridIntersection = false
    >
  class Viras {

    template<class Conf>
    friend class VirasTest;

  // START OF SYNTAX SUGAR STUFF

    template<class T>
    struct WithConfig { 
      Config* config; 
      T inner; 
      friend bool operator!=(WithConfig l, WithConfig r) 
      { return !(l == r); }
      friend std::ostream& operator<<(std::ostream& out, WithConfig const& self)
      { return out << outputPtr(self.inner); }
      DERIVE_TUPLE(WithConfig, inner)
      DERIVE_TUPLE_EQ
      DERIVE_TUPLE_LESS
    };

    struct Term : public WithConfig<typename Config::Term> { };
    struct Numeral : public WithConfig<typename Config::Numeral> {};
    struct Var : public WithConfig<typename Config::Var> {};
    struct Literal : public WithConfig<typename Config::Literal> {
      Term term() const
      { return Term {this->config, this->config->term_of_literal(this->inner)}; }

      PredSymbol symbol() const
      { return this->config->symbol_of_literal(this->inner); }

      friend std::ostream& operator<<(std::ostream& out, Literal const& self)
      { return out << self.term() << " " << self.symbol() << " 0"; }
    };
    struct Literals : public WithConfig<typename Config::Literals> {
      auto size() const { return this->config->literals_size(this->inner); }
      auto operator[](size_t idx) const { 
        return Literal { this->config, this->config->literals_get(this->inner, idx) }; 
      }
    };

    ///////////////////////////////////////
    // PRIMARY OPERATORS
    ///////////////////////////////////////

    friend Term operator+(Term lhs, Term rhs) 
    {
      VIRAS_ASSERT(lhs.config == rhs.config);
      return Term {lhs.config, lhs.config->add(lhs.inner, rhs.inner)};
    }

    friend Term operator*(Numeral lhs, Term rhs) 
    {
      VIRAS_ASSERT(lhs.config == rhs.config);
      return Term {lhs.config, lhs.config->mul(lhs.inner, rhs.inner)};
    }

    friend Numeral operator*(Numeral lhs, Numeral rhs) 
    {
      VIRAS_ASSERT(lhs.config == rhs.config);
      return Numeral {lhs.config, lhs.config->mul(lhs.inner, rhs.inner)};
    }

    ///////////////////////////////////////
    // LIFTED OPERATORS
    ///////////////////////////////////////

    friend Numeral operator+(Numeral lhs, Numeral rhs) 
    { return Numeral { lhs.config, lhs.config->add(lhs.inner, rhs.inner)}; }

    friend Term operator+(Numeral lhs, Term rhs) 
    { return Term { rhs.config, lhs.config->term(lhs.inner)} + rhs; }

    friend Term operator+(Term lhs, Numeral rhs) 
    { return lhs + Term { rhs.config, rhs.config->term(rhs.inner), }; }

#define LIFT_INT_TO_NUMERAL(function, CType)                                              \
    LIFT_INT_TO_NUMERAL_L(function, CType)                                                \
    LIFT_INT_TO_NUMERAL_R(function, CType)                                                \


#define LIFT_INT_TO_NUMERAL_L(function, CType)                                            \
    friend auto function(int lhs, CType rhs)                                              \
    { return function(Numeral {rhs.config, rhs.config->numeral(lhs)}, rhs); }            \

#define LIFT_INT_TO_NUMERAL_R(function, CType)                                            \
    friend auto function(CType lhs, int rhs)                                              \
    { return function(lhs, Numeral {lhs.config, lhs.config->numeral(rhs)}); }            \

#define LIFT_INT_TO_NUMERAL(function, CType)                                              \
    LIFT_INT_TO_NUMERAL_L(function, CType)                                                \
    LIFT_INT_TO_NUMERAL_R(function, CType)                                                \

    LIFT_INT_TO_NUMERAL(operator+, Numeral)
    LIFT_INT_TO_NUMERAL(operator-, Numeral)
    LIFT_INT_TO_NUMERAL(operator*, Numeral)

    LIFT_INT_TO_NUMERAL(operator==, Numeral)
    LIFT_INT_TO_NUMERAL(operator!=, Numeral)
    LIFT_INT_TO_NUMERAL(operator<=, Numeral)
    LIFT_INT_TO_NUMERAL(operator>=, Numeral)
    LIFT_INT_TO_NUMERAL(operator< , Numeral)
    LIFT_INT_TO_NUMERAL(operator> , Numeral)

    LIFT_INT_TO_NUMERAL(operator+, Term)
    LIFT_INT_TO_NUMERAL(operator-, Term)
    LIFT_INT_TO_NUMERAL_L(operator*, Term)


     // MULTIPLICATION
     // DIVISION

    friend Term operator/(Term lhs, Numeral rhs) 
    { return (1 / rhs) * lhs; }

    friend Numeral operator/(Numeral lhs, Numeral rhs) 
    { return Numeral{ rhs.config, rhs.config->inverse(rhs.inner) } * lhs; }

    LIFT_INT_TO_NUMERAL_R(operator/, Term)
    LIFT_INT_TO_NUMERAL(operator/, Numeral)

     // MINUS

#define DEF_UMINUS(CType)                                                                 \
    friend CType operator-(CType x)                                                       \
    { return -1 * x; }                                                                    \

  DEF_UMINUS(Numeral)
  DEF_UMINUS(Term)

#define DEF_BMINUS(T1, T2)                                                                \
    friend auto operator-(T1 x, T2 y)                                                     \
    { return x + -y; }                                                                    \

  DEF_BMINUS(Numeral, Numeral)
  DEF_BMINUS(Term   , Numeral)
  DEF_BMINUS(Numeral, Term   )
  DEF_BMINUS(Term   , Term   )

     // ABS

    friend Numeral abs(Numeral x) 
    { return x < 0 ? -x : x; }

    friend Numeral num(Numeral x)
    { return Numeral { x.config, x.config->num(x.inner) }; }

    friend Numeral den(Numeral x) 
    { return Numeral { x.config, x.config->den(x.inner) }; }

    friend Numeral lcm(Numeral l, Numeral r)
    { 
      auto cn = [&](auto x) { return Numeral { l.config, x }; };
      return cn(l.config->lcm(num(l).inner, num(r).inner)) 
           / cn(l.config->gcd(den(l).inner, den(r).inner));  
    }

     // floor
    friend Term floor(Term x) 
    { return Term { x.config, x.config->floor(x.inner), }; }

    friend Term ceil(Term x) 
    { return -floor(-x); }


    friend Numeral floor(Numeral x) 
    { return Numeral { x.config, x.config->floor(x.inner), }; }

    // COMPARISIONS

    friend bool operator<=(Numeral lhs, Numeral rhs) 
    { return lhs.config->leq(lhs.inner, rhs.inner); }

    friend bool operator<(Numeral lhs, Numeral rhs) 
    { return lhs.config->less(lhs.inner, rhs.inner); }

    friend bool operator>=(Numeral lhs, Numeral rhs) 
    { return rhs <= lhs; }

    friend bool operator>(Numeral lhs, Numeral rhs) 
    { return rhs < lhs; }

#define INT_CMP(OP)                                                                       \
    friend bool operator OP (Numeral lhs, int rhs)                                       \
    { return lhs OP Numeral  { lhs.config, lhs.config->numeral(rhs), }; }                \
                                                                                          \
    friend bool operator OP (int lhs, Numeral rhs)                                       \
    { return Numeral  { rhs.config, rhs.config->numeral(lhs), } OP rhs; }                \

    friend Term quot(Term t, Numeral p) { return floor(t / p); }
    friend Term rem(Term t, Numeral p) { return t - p * quot(t, p); }

    friend Term subs(Term self, Var var, Term by) {
      return matchTerm(self, 
        /* var y */ [&](auto v) { return v == var ? by : self; }, 

        /* numeral 1 */ [&]() { return self; }, 
        /* k * t */ [&](auto k, auto t) { return k * subs(t, var, by); }, 

        /* l + r */ [&](auto l, auto r) { 
          return subs(l,var,by) + subs(r,var,by);
        }, 

        /* floor */ [&](auto t) { return floor(subs(t,var,by)); });
    }


    static Term to_term(Numeral n) 
    { return Term { n.config, n.config->term(n.inner), }; }

    static Numeral to_numeral(Config* c, int n) 
    { return Numeral { c, c->numeral(n), }; }

#define LIFT_NUMERAL_TO_TERM_L(fn)                                                        \
    friend auto fn(Numeral const& lhs, Term const& rhs)                                 \
    { return fn(to_term(lhs), rhs); }

#define LIFT_NUMERAL_TO_TERM_R(fn)                                                        \
    friend auto fn(Term const& lhs, Numeral const& rhs)                                 \
    { return fn(lhs, to_term(rhs)); }

#define LIFT_NUMERAL_TO_TERM(fn)                                                          \
    LIFT_NUMERAL_TO_TERM_L(fn)                                                            \
    LIFT_NUMERAL_TO_TERM_R(fn)                                                            \


#define LITERAL_CONSTRUCTION_OPERATOR(fn, Sym)                                            \
    friend Literal fn(Term lhs, Term rhs)                                              \
    {                                                                                     \
      VIRAS_ASSERT(lhs.config == rhs.config);                                             \
      return Literal { lhs.config, lhs.config->create_literal((lhs - rhs).inner, Sym) }; \
    }                                                                                     \
                                                                                          \
    LIFT_NUMERAL_TO_TERM(fn)                                                              \
    LIFT_INT_TO_NUMERAL(fn, Term)                                                        \

    LITERAL_CONSTRUCTION_OPERATOR(operator> , PredSymbol::Gt);
    LITERAL_CONSTRUCTION_OPERATOR(operator>=, PredSymbol::Geq);
    LITERAL_CONSTRUCTION_OPERATOR(eq, PredSymbol::Neq);
    LITERAL_CONSTRUCTION_OPERATOR(neq, PredSymbol::Eq);

    // END OF SYNTAX SUGAR STUFF


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

    template<class IfVar, class IfOne, class IfMul, class IfAdd, class IfFloor>
    friend auto matchTerm(Term t, 
        IfVar   if_var, 
        IfOne   if_one, 
        IfMul   if_mul, 
        IfAdd   if_add, 
        IfFloor if_floor
        ) -> decltype(auto) {
      return t.config->matchTerm(t.inner,
        [&](auto x) { return if_var(Var{ t.config, x }); }, 
        [&]() { return if_one(); }, 
        [&](auto l, auto r) { return if_mul(Numeral{t.config, l},Term{t.config, r}); }, 
        [&](auto l, auto r) { return if_add(Term{t.config, l},Term{t.config, r}); }, 
        [&](auto x) { return if_floor(Term{t.config, x}); }
           );
    }

    Numeral numeral(int i)  { return Numeral { &_config, _config.numeral(i)}; }
    Term    term(Numeral n) { return Term    { &_config, _config.term(n.inner) }; }
    Term    term(Var v)     { return Term    { &_config, _config.term(v.inner) }; }
    Term    term(int i)     { return term(numeral(i)); }

    // TODO guard with macro
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

    // template<class MatchRec>
    // Numeral calcDeltaY(LiraTerm const& self, Var const& x, MatchRec matchRec) {
    //    return self.per == 0 
    //      ? numeral(0) 
    //      : matchRec(
    //     /* var y */ [&](auto y) 
    //     { return numeral(0); },
    //
    //     /* numeral 1 */ [&]() 
    //     { return numeral(0); },
    //
    //     /* k * t */ [&](auto k, auto t, auto rec) 
    //     { return  abs(k) * rec->deltaY; }, 
    //
    //     /* l + r */ [&](auto l, auto r, auto& rec_l, auto& rec_r) 
    //     { return rec_l.deltaY + rec_r.deltaY; },
    //
    //     /* floor t */   [&](auto t, auto& rec) 
    //     { return rec.deltaY + 1; }
    //     );
    // }


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
                                 | iter::dbg("lra term")
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
                       | iter::dbg("ebreak")
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
                                         
                                 | iter::dbg("ezero")
                       ; };
                       auto eseg         = [&]() { 
                         return 
                           iter::if_then_(t.sslp == 0 || ( t.sslp < 0 && isIneq(symbol)), breaks_plus_epsilon())
                                 else_if_(t.sslp >  0 && symbol == PredSymbol::Geq, iter::concat(breaks_plus_epsilon(), ezero()))
                                 else_if_(t.sslp >  0 && symbol == PredSymbol::Gt , iter::concat(breaks_plus_epsilon(), ezero() | iter::map([](auto x) { return x + epsilon; })))
                                 else_if_(t.sslp != 0 && symbol == PredSymbol::Neq, iter::concat(breaks_plus_epsilon(), ezero() | iter::map([](auto x) { return x + epsilon; })))
                                 else_is_(t.sslp != 0 && symbol == PredSymbol::Eq,  ezero())
                                 | iter::dbg("eseg")
                       ; };
                       auto ebound_plus  = [&]() { return 
                           iter::if_then_(lit.lim_pos_inf(), iter::vals<VT>(t.distXplus(), t.distXplus() + epsilon))
                                 else____(                   iter::vals<VT>(t.distXplus()                         ))
                                 | iter::dbg("ebound_plus")
                                 ; };

                       auto ebound_minus = [&]() { return 
                           iter::if_then_(lit.lim_neg_inf(), iter::vals<VT>(t.distXminus(), -infty))
                                 else____(                   iter::vals<VT>(t.distXminus()        ))
                                 | iter::dbg("ebound_minus")
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
      // VIRAS_LOG("substituting " << lit << "[ " << x << " // " << vt << " ]")
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
      VIRAS_LOG("substituting " << lit << "[ " << x << " // " << vt << " ] = " << res)
      return res;
    }


    auto vsubs_aperiodic1(std::vector<LiraLiteral> const& lits, Var x, VirtualTerm term) {
      // VIRAS_LOG((lits) << "[ " << x << " // " << vt << " ]")
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
                                         | iter::dbg("fin");
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
        | iter::dbg("elim set: ")
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
