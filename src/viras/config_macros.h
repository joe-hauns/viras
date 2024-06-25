#pragma once

#ifndef VIRAS_ASSERT
#  include <cassert>
#  define VIRAS_ASSERT(...) assert(__VA_ARGS__);
#endif


#ifndef VIRAS_DEBUG_LEVEL
#  define VIRAS_DEBUG_LEVEL 0
#endif

template<class... As>
void __viras_log_all(As const& ... as) { (std::cout << ... << as); }
#define __VIRAS_LOG(...) __viras_log_all("[ viras ] ", __FILE__, "\t@ ", __LINE__, ":\t", __VA_ARGS__, "\n");


#ifndef VIRAS_LOG
#  define VIRAS_LOG(lvl, ...) if (lvl < VIRAS_DEBUG_LEVEL) { __VIRAS_LOG(__VA_ARGS__) }
#endif 

#ifndef DBGE
#  define DBGE(expr) __VIRAS_LOG(#expr, " = ", expr)
#endif

