#pragma once
#include "viras/config_macros.h"

#include "viras/output.h"
#include "viras/base_types.h"
#include "viras/api.h"
#include "viras/iter.h"
#include "viras/derive.h"
#include "viras/predicate.h"
#include "viras/virtual_term.h"
#include "viras/lira_literal.h"
#include "viras/break.h"


namespace viras {

  template<class C>
  class Viras
  {

    template<class Conf>
    friend class VirasTest;

    C _config;

    static constexpr Infty infty { .positive = true, };

    ZComp<C> Z(Numeral<C> n) { return ZComp<C>(n); }
    ZComp<C> Z(int n) { return ZComp<C>(numeral(n)); }
    ZComp<C> Z(int n, int m) { return ZComp<C>(numeral(n) / m); }

    Numeral<C> numeral(int i)  { return Numeral<C> { &_config, _config.numeral(i)}; }
    Term<C>    term(Numeral<C> n) { return Term<C>    { &_config, _config.term(n.inner) }; }
    Term<C>    term(Var<C> v)     { return Term<C>    { &_config, _config.term(v.inner) }; }
    Term<C>    term(int i)     { return term(numeral(i)); }

    Var<C> test_var(const char* name) { return Var<C> { &_config, _config.test_var(name) }; }


  public:
    using Config = C;
    Viras(C c) : _config(std::move(c)) { };

    ~Viras() {};

    // TODO make it possible to fail gracefully with uniterpreted stuff

  private:
    std::vector<LiraLiteral<C>> analyse(Literals<C> const& self, Var<C> x)
    {
      return iter::array(self)
        | iter::map([&](auto lit) { return LiraLiteral<C>::analyse(lit, x); })
        | iter::collect_vec;
    }

    std::vector<LiraLiteral<C>> analyse(typename C::Literals const& self, typename C::Var x)
    { return analyse(Literals<C> { &_config, self }, Var<C> { &_config, x }); }

    static constexpr Epsilon epsilon{};

    auto elim_set(Var<C> const& x, LiraLiteral<C> const& lit)
    {
      auto& t = lit.term;
      // auto& x = t.x;
      auto symbol = lit.symbol;
      auto isIneq = [](auto symbol) { return (symbol == PredSymbol::Geq || symbol == PredSymbol::Gt); };
      using VT = VirtualTerm<C>;

      return iter::if_then_(t.breaks.empty(),
                           iter::if_then_(t.sslp == 0              , iter::vals<VT>(-infty))
                                 else_if_(symbol == PredSymbol::Neq, iter::vals<VT>(-infty, t.zero(term(0)) + epsilon))
                                 else_if_(symbol == PredSymbol:: Eq, iter::vals<VT>(t.zero(term(0))))
                                 else_if_(t.sslp < 0               , iter::vals<VT>(-infty))
                                 else_if_(symbol == PredSymbol::Geq, iter::vals<VT>(t.zero(term(0))))
                                 else_is_(symbol == PredSymbol::Gt , iter::vals<VT>(t.zero(term(0)) + epsilon))
                                 | iter_dbg(1, "  lra term")
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
                                           | iter::flat_map([&](auto* b) { return intersectGrid(Break<C>(t.zero(b->t), abs(1 - t.oslp / t.sslp)),
                                                                                                Bound::Open, t.distXminus(), t.deltaX(), Bound::Open); })
                                           | iter::map([&](auto t) { return VT(t); }))
                       ; };
                       auto eseg         = [&]() {
                         return
                           iter::if_then_(t.sslp == 0 || ( t.sslp < 0 && isIneq(symbol)), breaks_plus_epsilon())
                                 else_if_(t.sslp >  0 && symbol == PredSymbol::Geq, iter::concat(breaks_plus_epsilon(), ezero()))
                                 else_if_(t.sslp >  0 && symbol == PredSymbol::Gt , iter::concat(breaks_plus_epsilon(), ezero() | iter::map([](auto x) { return x + epsilon; })))
                                 else_if_(t.sslp != 0 && symbol == PredSymbol::Neq, iter::concat(breaks_plus_epsilon(), ezero() | iter::map([](auto x) { return x + epsilon; })))
                                 else_is_(t.sslp != 0 && symbol == PredSymbol::Eq,  ezero())
                       ; };
                       auto ebound_plus  = [&]() { return
                           iter::if_then_(lit.lim(infty), iter::vals<VT>(t.distXplus(), t.distXplus() + epsilon))
                                else____(                   iter::vals<VT>(t.distXplus()                         ))
                                 ; };

                       auto ebound_minus = [&]() { return
                           iter::if_then_(lit.lim(-infty), iter::vals<VT>(t.distXminus(), -infty))
                                 else____(                   iter::vals<VT>(t.distXminus()        ))
                       ; };

#define _elem(elem) elem() | iter_dbg(0, "elimset (", std::setw(12), #elem,  ") of ", lit, "@", x)
                       return iter::if_then_(t.periodic(), iter::concat( _elem(ebreak), _elem(eseg)))
                                    else____(              iter::concat( _elem(ebreak), _elem(eseg), _elem(ebound_plus), _elem(ebound_minus)));
// #undef _elem
                   }());
    }

    auto elim_set(Var<C> const& x, std::vector<LiraLiteral<C>> const& lits)
    { return iter::array(lits)
        | iter::flat_map([&](auto lit) { return elim_set(x, *lit); })
        | iter::dedup(); }

    Literal<C> literal(Term<C> t, PredSymbol s)
    { return Literal<C> { &_config, _config.create_literal(t.inner, s), }; }

    Literal<C> literal(bool b) { return literal(term(0), b ? PredSymbol::Eq : PredSymbol::Neq); }

    Literal<C> vsubs_aperiodic(LiraLiteral<C> const& lit, Var<C> x, VirtualTerm<C> vt)
    {
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
          return vsubs_aperiodic(lit, x, vt);
        } else {
          return literal(lit.lim(*vt.infty));
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
        VIRAS_UNREACHABLE

      } else {
        VIRAS_ASSERT(!vt.epsilon && !vt.infty && !vt.period);
        return literal(subs(s.self, x, *vt.term), symbol);
      }
      };
      auto res = impl();
      VIRAS_LOG(2, "substituting ( ", lit, " )[ ", x, " // ", vt, " ] = ", res)
      return res;
    }


    auto vsubs_aperiodic(std::vector<LiraLiteral<C>> const& lits, Var<C> x, VirtualTerm<C> term)
    {
      VIRAS_ASSERT(!term.period);
          /* case 2 */
      return iter::array(lits)
        | iter::map([this, x, term](auto lit) { return this->vsubs_aperiodic(*lit, x, term); });
    }

    auto vsubs(std::vector<LiraLiteral<C>> const& lits, Var<C> x, VirtualTerm<C> vt) {
      return iter::if_then_(vt.period, ([&](){
                              /* case 1 */
                              auto A = [&lits]() { return iter::array(lits) | iter::filter([](auto l) { return !l->periodic(); }); };
                              auto P = [&lits]() { return iter::array(lits) | iter::filter([](auto l) { return l->periodic(); }); };

                              VIRAS_ASSERT((P() | iter::count()) > 0); // if there are no periodic literals we cannot have periodic solution terms
                              Numeral<C> lambda = *(P()
                                             | iter::map([&](auto L) { return L->term.per; })
                                             | iter::filter([](auto per) { return per != 0; })
                                             | iter::fold([](auto l, auto r) { return lcm(l, r); }));

                              auto iGrid = [ vt](auto... args) {
                                return intersectGrid(Break<C>(*vt.term, *vt.period), args...)
                                                    | iter::map([vt](auto x) { return VirtualTerm<C>(x) + vt.epsilon; });
                                ; };
                              auto all_lim_top = [A](Infty inf) { return A() | iter::all([inf](auto l) { return l->lim(inf) == true; }); };
                              auto one_lambda_plus = [iGrid, vt, lambda](Infty inf) {
                                return iGrid(Bound::Closed, *vt.term, lambda, Bound::Open)
                                     | iter::map([=](auto s) { return s + inf; });
                              };
                              std::optional<LiraLiteral<C> const*> aperiodic_equality;
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
                                         | iter_dbg(2, "  fin");
                              return std::move(fin)
                              | iter::map([this,&lits,x](auto t) { return this->vsubs_aperiodic(lits, x, t); });
                            }()))
                   else____( ([&]() {
                         auto out = iter::vals(vsubs_aperiodic(lits, x, vt));
                         return out;
                       }()));
    }

    auto quantifier_elimination(Var<C> const& x, std::vector<LiraLiteral<C>> const& lits)
    { return elim_set(x, lits)
        | iter::flat_map([this,&lits,x](auto t) { return vsubs(lits, x, t); }); }

  public:
    auto quantifier_elimination(typename C::Var x, typename C::Literals ls)
    {
      auto lits = std::make_unique<std::vector<LiraLiteral<C>>>(analyse(ls, x));
      auto lits_ptr = lits.get();
      auto var = std::make_unique<Var<C>>(Var<C> { &_config, x });
      auto var_ptr = var.get();
      return quantifier_elimination(*var_ptr, *lits_ptr)
        | iter::store_value(std::move(lits))
        | iter::store_value(std::move(var))
        | iter::map([&](auto lits) { return std::move(lits) | iter::map([](auto lit) { return lit.inner; }); });
    }

  };

  template<class Api, class Opts = DefaultOpts>
  auto viras(Api api, Opts opts = Opts())
  { return Viras<Config<Api, Opts>>(Config<Api, Opts>(std::move(api), std::move(opts) )); }


}
