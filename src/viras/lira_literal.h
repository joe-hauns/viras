#pragma once
#include "viras/lira_term.h"
#include "viras/virtual_term.h"
#include "viras/iter.h"
#include "viras/break.h"

namespace viras {

  template<class C>
  struct LiraLiteral 
  {
    LiraTerm<C> term;
    PredSymbol symbol;

    bool periodic() const { return term.periodic(); }

    bool lim(Infty i) const
    { 
      VIRAS_ASSERT(term.oslp != 0);
      switch (symbol) {
      case PredSymbol::Gt:
      case PredSymbol::Geq: return i.positive ? term.oslp > 0 
                                              : term.oslp < 0;
      case PredSymbol::Neq: return true;
      case PredSymbol::Eq: return false;
      }
      VIRAS_UNREACHABLE
    }

    static LiraLiteral analyse(Literal<C> const& self, Var<C> x) 
    { return LiraLiteral { LiraTerm<C>::analyse(self.term(), x), self.symbol() }; }

    friend std::ostream& operator<<(std::ostream& out, LiraLiteral const& self)
    { return out << self.term << " " << self.symbol << " 0"; }
  };
} // namespace viras
