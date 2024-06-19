#pragma once

#ifndef VIRAS_ASSERT
#include <cassert>
#define VIRAS_ASSERT(...) assert(__VA_ARGS__);
#endif // VIRAS_ASSERT


#ifndef VIRAS_DEBUG_LEVEL
#define VIRAS_DEBUG_LEVEL 0
#endif

#ifndef VIRAS_LOG
template<class... As>
void __viras_log_all(As const& ... as) { (std::cout << ... << as); }
#define VIRAS_LOG(lvl, ...) if (lvl < VIRAS_DEBUG_LEVEL) { __viras_log_all("[ viras ] ", __FILE__, "\t@ ", __LINE__, ":\t", __VA_ARGS__, "\n"); }
#endif // VIRAS_ASSERT


