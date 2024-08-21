#pragma once

#ifndef VIRAS_ASSERT
#  include <cassert>
#  define VIRAS_ASSERT(...) assert(__VA_ARGS__);
#endif


#ifndef VIRAS_DEBUG_LEVEL
#  define VIRAS_DEBUG_LEVEL 0
#endif

#ifndef  VIRAS_OUTPUT
   template<class... As>
   void __viras_log_all(As const& ... as) { (std::cout << ... << as); }

#  define VIRAS_OUTPUT(...)  \
     __viras_log_all("[ viras ] ", __FILE__, "\t@ ", __LINE__, ":\t", __VA_ARGS__, "\n");
#endif


#define VIRAS_LOG(lvl, ...) if (lvl < VIRAS_DEBUG_LEVEL) { VIRAS_OUTPUT(__VA_ARGS__) }

#ifndef DBGE
#  define DBGE(expr) __VIRAS_LOG(#expr, " = ", expr)
#endif

#ifndef VIRAS_UNREACHABLE
#  define VIRAS_UNREACHABLE VIRAS_ASSERT(false) while (true) {}
#endif
