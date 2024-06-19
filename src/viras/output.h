#pragma once
#include "viras/config_macros.h"

#include <iostream>
#include <sstream>


namespace viras {

namespace output {

  template<class C>
  struct OutputPtr  { C const& self; };
  template<class C>
  OutputPtr<C> ptr(C const& c)  { return OutputPtr<C> { c }; }

  template<class C>
  std::ostream& operator<<(std::ostream& out, OutputPtr<C*> const& self)
  { return self.self == nullptr ? out << "nullptr" : out << *self.self; }

  template<class C>
  std::ostream& operator<<(std::ostream& out, OutputPtr<C> const& self)
  { return out << self.self; }

};

  template<class A>
  std::ostream& operator<<(std::ostream& out, std::vector<A> const& v) {
    out << "[ ";
    auto fst = true;
    for (auto& x : v) {
      if (fst) {
        fst = false;
      } else {
        out << ", ";
      }
      out << x;
    }
    return out << " ]";
  }


  template<class... Ts> 
  std::string output_to_string(Ts const&... ts)
  { 
    std::stringstream out;
    (out << ... << ts);
    return out.str();
  }

};
