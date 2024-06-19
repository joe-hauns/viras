#pragma once
#include <iostream>

namespace viras {
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
}
