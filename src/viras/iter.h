#pragma once

#include "viras/output.h"
#include <set>
#include <optional>
#include <tuple>
#include <vector>

namespace viras {
   namespace iter {


  template<class T>
  T dummyVal();

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

    template<class Iter>
    struct StlForeachLoopIterable {
      Iter iter;
      struct Begin {
        Iter& iter;
        std::optional<value_type<Iter>> cur;
        void operator++() { cur = iter.next(); }
        value_type<Iter> operator*() { return std::move(*cur); }
      };
      struct End {
        friend bool operator!=(Begin const& begin, End const& end) {
          return bool(begin.cur);
        }
      };
      Begin begin() { return { .iter = iter, .cur = iter.next(), }; }
      End end() { return {}; }
    };

    constexpr auto std_for = 
      iterCombinator([](auto iter) {
          return StlForeachLoopIterable<decltype(iter)> { std::move(iter) };
      });


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

#define iter_dbg(lvl, ...) ::viras::iter::inspect([=](auto x) { VIRAS_LOG(lvl, __VA_ARGS__, ": ", output::ptr(x)); })
    template<class M>
    auto dbg(M msg) {
      return inspect([msg = std::move(msg)](auto x) { VIRAS_LOG(msg, ": ", outputPtr(x)); });
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
} // namespace viras


