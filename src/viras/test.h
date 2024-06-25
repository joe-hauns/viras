#pragma once
#include "viras.h"
#include "viras/iter.h"
#include <regex>

namespace viras {


template<class A>
bool is_set_equal(std::vector<A> const& lhs, std::vector<A> const& rhs) {
  auto find_missing = [](auto& l, auto& r) {
    return iter::array(l)
      | iter::find([&](auto* x) {
          return !(iter::array(r)
            | iter::any([&](auto* y) { return *x == *y; }));
            });
  };
  if (find_missing(lhs, rhs)) {
    return false;
  } else if (find_missing(rhs, lhs)) {
    return false;
  } else {
    return true;
  }
}

template<class C>
struct VirasTest : Viras<C> 
{

  template<class... As>
  VirasTest(As... as) : Viras<C>(as...) {}

  using Viras<C>::epsilon;
  using Viras<C>::Z;
  using Viras<C>::infty;
  using Viras<C>::term;
  using Viras<C>::numeral;

  public:

  struct SetEqual {
    std::vector<VirtualTerm<C>> expected;

    std::optional<std::string> check(std::vector<VirtualTerm<C>> const& result) {
      for (auto s : iter::array(expected) | iter::std_for) {
        if (!(iter::array(result) | iter::any([&](auto* res) { return *res == *s; })) ) {
          return output_to_string("not found: ", s);
        }
      }
      for (auto s : iter::array(result) | iter::std_for) {
        if (!(iter::array(expected) | iter::any([&](auto* exp) { return *exp == *s; })) ) {
          return output_to_string("unexpected term in result: ", s);
        }
      }
      return {};
    }
    friend std::ostream& operator<<(std::ostream& out, SetEqual const& self)
    { return out << "set equal: " << self.expected; }
  };



  struct AllContained {
    std::vector<VirtualTerm<C>> expected;

    std::optional<std::string> check(std::vector<VirtualTerm<C>> const& result) {
      for (auto& s : arrayIter(expected)) {
        if (!arrayIter(result).any([&](auto& res) { return res == s; }) ) {
          return output_to_string("not found: ", s);
        }
      }
      return {};
    }
    friend std::ostream& operator<<(std::ostream& out, AllContained const& self)
    { return out << "contains: " << self.expected; }
  };


  using ExpectedCheckVar = std::variant<AllContained, SetEqual>;
  struct ExpectedCheck :  ExpectedCheckVar
  {
    // using ExpectedCheckVar::variant;
    ExpectedCheck(AllContained x) : ExpectedCheckVar(std::move(x)) {}
    ExpectedCheck(SetEqual     x) : ExpectedCheckVar(std::move(x)) {}

    std::optional<std::string> check(std::vector<VirtualTerm<C>> const& result) 
    { return std::visit([&](auto& x) { return x.check(result); }, *this); }
    friend std::ostream& operator<<(std::ostream& out, ExpectedCheck const& self)
    { std::visit([&](auto& self) { out << self; }, self); return out; }
  };

  template<class... As>
  ExpectedCheck containsAll(As... as)
  { return ExpectedCheck(AllContained{std::vector<VirtualTerm<C>>{VirtualTerm<C>(as)...}}); }

  ExpectedCheck set_equal(std::vector<VirtualTerm<C>> terms)
  { return ExpectedCheck(SetEqual{std::move(terms)}); }


  template<class... As>
  ExpectedCheck set_equal(As... as)
  { return ExpectedCheck(SetEqual{std::vector<VirtualTerm<C>>{VirtualTerm<C>(as)...}}); }


  struct ElimSetTest {
    Var<C> x;
    std::vector<Literal<C>> conj;
    ExpectedCheck expected;

    std::optional<std::string> run(Viras<C>& viras)
    {
      auto analysed = iter::array(conj) 
        | iter::map([&](auto l) { return viras.analyse(*l, x); })
        | iter::collect_vec;
      auto result = viras.elim_set(x, analysed) | iter::collect_vec;
      auto error = expected.check(result);
      if (error) {
        return std::optional<std::string>(
            output_to_string(
              "[    input ] ", conj, "\n",
              "[   result ] ", result, "\n",
              "[    error ] ", *error, "\n",
              "[ expected ] ",    expected, "\n"
              )
            );
      } else {
        return std::optional<std::string>();
      }
    }
  };


  struct TermAnalysisTest {
    using TestFun = std::function<std::optional<std::string>(Term<C>, LiraTerm<C>&)>;
    Var<C> x;
    Term<C> term;
    std::vector<TestFun> expected;

    std::optional<std::string> run(Viras<C>& viras)
    {
      auto result = viras.analyse(term, x);
      for (auto& c : expected) {
        auto res = c(term, result);
        if (res) {
          return res;
        }
      }
      return std::optional<std::string>();
    }
  };

  using Test = std::variant<ElimSetTest, TermAnalysisTest>;

  bool run_test(std::pair<std::string, Test>& testCase) {
    auto& [name, test] = testCase;
    auto err = std::visit([&](auto& t) { return t.run(*this); }, test);
    if (err) {
      std::cout << "[ FAIL ] " << name << std::endl;
      std::cout << *err << std::endl;
      return false;
    } else {
      std::cout << "[  OK  ] " << name << std::endl;
      return true;
    }
  }

  bool run_tests(std::regex regex) {
    bool success = true;
    for (auto& testCase : tests()) {
      if (std::regex_match(testCase.first, regex)) {
        success &= run_test(testCase);
      }
    }
    return success;
  }

  auto run_tests(const char* regex) { return run_tests(std::basic_regex(regex)); }
  auto run_test (const char* test)  { return run_test(std::string(test)); }

  bool run_test(std::string const& name){
    auto success = true;
    for (auto& testCase : tests()) {
      if (testCase.first == name) {
        success &= run_test(testCase);
      }
    }
    return success;
  }


  bool auto_test(){
    if (std::getenv("VIRAS_TEST_NAME")) {
      return run_test(std::getenv("VIRAS_TEST_NAME"));
    } else if (std::getenv("VIRAS_TEST_PATTERN")) {
      return run_tests(std::getenv("VIRAS_TEST_PATTERN"));
    } else {
      return run_tests(".*");
    }
  }

  template<class... As>
  auto breakSet(As... as)
  { return std::vector<Break<C>> { Break<C>{ *as.term, *as.period }... }; }


  template<class... Tests> 
  auto allPass(Tests... ts) 
  { return std::vector<typename TermAnalysisTest::TestFun> { typename TermAnalysisTest::TestFun(ts)... }; }

  std::vector<std::pair<std::string, Test>> tests() {
    std::vector<std::pair<std::string, Test>> tests;

    auto x_var = this->test_var("x");
    auto x = term(x_var);
    auto a = term(this->test_var("a"));
    auto b = term(this->test_var("b"));
    auto c = term(this->test_var("c"));
    auto frac = [&](auto l, auto r) { return numeral(l) / r; };
    std::vector<Term<C>> const_terms = { 
        a 
      , a + b
      , 0 * x 
      , x + a - x
      , floor(x) + a - floor(x) 
    };
    // std::vector<Term<C>> _linear_terms_pos_slope = { 
    //     a + frac(1,2) * x
    //   , a + 2 * x + b + 3 * x
    //   , 0 * x + a + x
    //   , 2 * x + a - x 
    //   , floor(x) + a - floor(x)  + frac(1,2) * x
    // };
    //
    // auto linear_terms_pos_slope = [&]() { return 
    //   iter::array(_linear_terms_pos_slope) | iter::map([](auto* x) { return *x; }); };
    //
    // auto linear_terms_neg_slope = [&]() { return 
    //   linear_terms_pos_slope() | iter::map([](auto t) { return -t; }); };
    //
    // auto linear_terms_non_zero_slope = []() { return
    //   iter::concat(linear_terms_pos_slope(), linear_terms_neg_slope()); };

#define DEF_TEST(name, ...)                                                               \
    {                                                                                     \
      auto test = __VA_ARGS__;                                                            \
      test.x = x_var;                                                                     \
      tests.push_back(std::make_pair(#name, std::move(test)));                            \
    }                                                                                     \

#define TEST_EQ(lhs, rhs)  TEST_CMP(lhs,==,rhs)
#define TEST_GT(lhs, rhs)  TEST_CMP(lhs,>,rhs)
#define TEST_GEQ(lhs, rhs)  TEST_CMP(lhs,>=,rhs)
#define TEST_LEQ(lhs, rhs)  TEST_CMP(lhs,<=,rhs)
#define TEST_LT(lhs, rhs)  TEST_CMP(lhs,<,rhs)



#define TEST_F(FUN, lhs, rhs)                                                            \
  [=](auto input, LiraTerm<C>& result) -> std::optional<std::string> {                    \
    if(FUN(lhs, rhs))  {                                                                     \
      return std::optional<std::string>();                                                \
    } else {                                                                              \
      return output_to_string(                                                            \
          "[    input ] ", input, "\n",                                                   \
          "[    query ] ", #lhs, "\n",                                                    \
          "[    value ] ", lhs, "\n",                                                     \
          "[ expected ] " #FUN " ", rhs, "\n"                                              \
          );                                                                              \
    }                                                                                     \
  }

#define TEST_CMP(lhs, OP, rhs)                                                            \
  [=](auto input, LiraTerm<C>& result) -> std::optional<std::string> {                    \
    if(lhs OP rhs)  {                                                                     \
      return std::optional<std::string>();                                                \
    } else {                                                                              \
      return output_to_string(                                                            \
          "[    input ] ", input, "\n",                                                   \
          "[    query ] ", #lhs, "\n",                                                    \
          "[    value ] ", lhs, "\n",                                                     \
          "[ expected ] " #OP " ", rhs, "\n"                                              \
          );                                                                              \
    }                                                                                     \
  }


    DEF_TEST(lra_01, 
        ElimSetTest {
          .conj = { x > 3 },
          .expected = containsAll( term(3) + epsilon ),
        })

    DEF_TEST(lra_02, 
        ElimSetTest {
          .conj = { 3 > x },
          .expected = containsAll( -infty ),
        })

    DEF_TEST(lra_03, 
        ElimSetTest {
          .conj = { x >= 3 },
          .expected = containsAll( term(3) ),
        })

    DEF_TEST(lra_04, 
        ElimSetTest {
          .conj = { 3 >= x },
          .expected = containsAll( -infty ),
        })

    DEF_TEST(lra_05, 
        ElimSetTest {
          .conj = { b > x, x > a },
          .expected = containsAll( -infty, a + epsilon ), 
        })

    DEF_TEST(lra_06, 
        ElimSetTest {
          .conj = { b > x, x >= a },
          .expected = containsAll( a, -infty ), 
        })

    DEF_TEST(lra_07, 
        ElimSetTest {
          .conj = { b >= x, x >= a },
          .expected = containsAll( a, -infty ), 
        })

    DEF_TEST(floor_1, 
        ElimSetTest {
          .conj = { eq(floor(x), x) },
          .expected = containsAll( 0 + Z(1) ), 
        })

    DEF_TEST(floor_2, 
        ElimSetTest {
          .conj = { floor(x) > x },
          .expected = containsAll( 0 + Z(1), term(0) + epsilon + Z(1) ),  
        })

    DEF_TEST(floor_2_inv, 
        ElimSetTest {
          .conj = { x >= floor(x) },
          .expected = containsAll( 0 + Z(1), term(0) + epsilon + Z(1) ),  
        })

    DEF_TEST(floor_3, 
        ElimSetTest {
          .conj = { eq(floor(x - a), x) },
          .expected = containsAll( a + Z(1) ), 
        })

    DEF_TEST(floor_3_props, 
        TermAnalysisTest {
          .term =  floor(x + a),
          .expected = allPass( TEST_EQ(result.per   , 1)
                             , TEST_EQ(result.deltaY, 1)
                             , TEST_EQ(result.breaks,  breakSet( -a + Z(1)))
                             )
        })

    DEF_TEST(floor_4, 
        ElimSetTest {
          .conj = { eq(floor(x - a), x) },
          .expected = containsAll( a + Z(1) ), 
        })

    DEF_TEST(floor_5, 
        ElimSetTest {
          .conj = { eq(floor(x - a), x) },
          .expected = containsAll( a + Z(1) ), 
        })

    DEF_TEST(motivating_test,
        ElimSetTest {
          .conj = { 
            floor( x ) - 1 >= 0
          },
          .expected = containsAll( term(1) ), 
        })

    DEF_TEST(motivating_test_prop,
        TermAnalysisTest {
          .term =  floor(x) - 1,
          .expected = allPass( TEST_EQ(result.per   , 1)
                             , TEST_EQ(result.distYminus, term(-2))
                             , TEST_EQ(result.deltaY    ,  1)
                             , TEST_EQ(result.breaks,  breakSet( term(0) + Z(1)))
                             )
        })

    DEF_TEST(motivating_test_prop,
        TermAnalysisTest {
          .term =  floor(x),
          .expected = allPass( TEST_EQ(result.per       , 1)
                             , TEST_EQ(result.distYminus, term(-1))
                             , TEST_EQ(result.deltaY    , 1)
                             , TEST_EQ(result.breaks,  breakSet( term(0) + Z(1)))
                             )
        })

    DEF_TEST(motivating_test_prop,
        TermAnalysisTest {
          .term =  x,
          .expected = allPass( TEST_EQ(result.per       , 0)
                             , TEST_EQ(result.distYminus, term(0))
                             , TEST_EQ(result.deltaY    , 0)
                             )
        })

    DEF_TEST(motivating_test_3,
        ElimSetTest {
          .conj = { floor( x ) - 1 > 0 },
          .expected = containsAll( term(2) ), 
        })

    DEF_TEST(motivating_test_4,
        ElimSetTest {
          .conj = { -floor( -x ) - 1 > 0 },
          .expected = containsAll( numeral(1) + epsilon ), 
        })

    DEF_TEST(motivating_test_5,
        ElimSetTest {
          .conj = { eq(-floor( -x ) - 1, 0) },
          .expected = containsAll( numeral(1) ), 
        })

    DEF_TEST(motivating_test_2,
        ElimSetTest {
          .conj = { floor( x ) - a >= 0 },
          .expected = containsAll( a /* if a is integral */ ,  floor(a) + 1 /* == ceil(a) if a is not integral */), 
        })

    DEF_TEST(some_props, 
        TermAnalysisTest {
          .term = -floor(-3 * x + a) - x,
          .expected = allPass( TEST_EQ(result.distYminus, -a)
                             , TEST_EQ(result.deltaY, 1)
                             , TEST_EQ(result.lim,  floor(3 * x - a) + 1 - x)
                             , TEST_EQ(result.breaks,  breakSet( frac(1,3) * a + Z(1,3)))
                             , TEST_EQ(result.distXminus(), frac(1,2) * (a - 1)  )
                             , TEST_EQ(result.deltaX(), frac(1,2)  )
                             )
        })

    DEF_TEST(some_props_2, 
        TermAnalysisTest {
          .term = floor(2 * (-floor(-3 * x + a) - x) - b),
          .expected = allPass( 
                               TEST_EQ(result.breaks,  breakSet( frac(1,3) * a + Z(1,3), -frac(1,2) * b + Z(1,2)
                                    ))
                             , TEST_EQ(result.per,     frac(1,1))
                             )
        })

    DEF_TEST(deep_breaks_1, 
        TermAnalysisTest {
          .term = floor(frac(1,2) * floor(x) + x),
          .expected = allPass( 
                               TEST_EQ(result.breaks,  breakSet( term(0) + Z(2)
                                                               , frac(3,2) + Z(2)
                                                               , term(0) + Z(1))) // TODO 0 + 1Z subset 0 + 2Z
                             , TEST_EQ(result.per,     numeral(2))
                             )
        })

    DEF_TEST(deep_breaks_2, 
        TermAnalysisTest {
          .term = floor(frac(1,2) * floor(x) + x - a),
          .expected = allPass( 
                               TEST_EQ(result.breaks,  breakSet(  // this was checked by manually verifying plots for different a
                                                          a + -1 * floor(a) + Z(2)
                                                        , a + frac(3,2) + -1 * floor(a + frac(1,2)) + Z(2)
                                                        , term(0) + Z(1) ))
                             , TEST_EQ(result.per,     numeral(2))
                             )
        })

    DEF_TEST(motivating_props_1, 
        TermAnalysisTest {
          .term = -x  - floor(-x),
          .expected = allPass(TEST_EQ(result.lim, -x + floor(x) + 1))
        })

    DEF_TEST(motivating, 
        ElimSetTest {
          .conj = { 
             -x  - floor(-x) >= c
          ,  x >= floor(a) + frac(1,3)
          , -x >= floor(a) + frac(2,3)
          },
          .expected = containsAll( numeral(0) + Z(1), floor(a) + frac(1,3), -infty ), 
        })


    for (auto t : const_terms) {
      for (auto lit : { t > 0, neq(t, 0), eq(t, 0), t >= 0 }) {
        DEF_TEST(breaks_lra_case_01, 
            ElimSetTest {
              .conj = { lit }, 
              .expected = containsAll( -infty ), 
            })
      }
    }

    {
      struct LinearTermTest {
        Term<C> term;
        Term<C> zero;
      };
      std::vector<LinearTermTest> lra_tests = {
            LinearTermTest 
            { .term = x + a        
            , .zero = -a             }
          , LinearTermTest 
            { .term = 2 * x + a    
            , .zero = -frac(1,2) * a }
          , LinearTermTest 
            { .term = x + floor(x) + a + floor(x) - 2*floor(x)
            , .zero = -a             }
          };

      for (auto t : lra_tests) {

        DEF_TEST(breaks_lra_case_02, 
            ElimSetTest {
              .conj = { neq(t.term, 0) }, 
              .expected = set_equal( -infty, t.zero + epsilon ), 
            })

        DEF_TEST(breaks_lra_case_02, 
            ElimSetTest {
              .conj = { neq(-t.term, 0) }, 
              .expected = set_equal( -infty, t.zero + epsilon ), 
            })

        DEF_TEST(breaks_lra_case_03, 
            ElimSetTest {
              .conj = { eq(t.term, 0) }, 
              .expected = set_equal( t.zero ), 
            })

        DEF_TEST(breaks_lra_case_03, 
            ElimSetTest {
              .conj = { eq(-t.term, 0) }, 
              .expected = set_equal( t.zero ), 
            })

        DEF_TEST(breaks_lra_case_04, 
            ElimSetTest {
              .conj = { t.term >= 0 }, 
              .expected = set_equal( t.zero ), 
            })

        DEF_TEST(breaks_lra_case_04, 
            ElimSetTest {
              .conj = { t.term > 0 }, 
              .expected = set_equal( t.zero + epsilon ), 
            })


        DEF_TEST(breaks_lra_case_04, 
            ElimSetTest {
              .conj = { -t.term >= 0 }, 
              .expected = set_equal( -infty ), 
            })

        DEF_TEST(breaks_lra_case_04, 
            ElimSetTest {
              .conj = { -t.term > 0 }, 
              .expected = set_equal( -infty ), 
            })

        DEF_TEST(analsis_test_pos,
            TermAnalysisTest {
              .term =  t.term,
              .expected = allPass( TEST_EQ(result.zero(term(0)), t.zero)
                                 , TEST_EQ(result.distYminus, -result.sslp * x + t.term )
                                 , TEST_EQ(result.deltaY    ,  0)
                                 , TEST_EQ(result.breaks    , breakSet())
                                 , TEST_GT(result.sslp    , 0)
                                 )
            })

        DEF_TEST(analsis_test_neg,
            TermAnalysisTest {
              .term =  -t.term,
              .expected = allPass( TEST_EQ(result.zero(term(0)), t.zero)
                                 , TEST_EQ(result.distYminus, -result.sslp * x - t.term )
                                 , TEST_EQ(result.deltaY    ,  0)
                                 , TEST_EQ(result.breaks    , breakSet())
                                 , TEST_LT(result.sslp    , 0)
                                 )
            })

      }
    }


    auto vt = [](auto& xs) { return iter::array(xs) | iter::map([](auto* t) { return VirtualTerm<C>(*t); }); };
    auto plus_epsilon = [&](auto& xs) { return vt(xs) | iter::map([](auto x) { return x + epsilon; }); };
    {
      struct PeriodicNonZeroSlopeTermTest {
        Term<C> term;
        std::vector<Break<C>> breaks;
        std::vector<Break<C>> zeros;
      };
      std::vector<PeriodicNonZeroSlopeTermTest> lira_tests = {
        { .term = x - floor(x)
        , .breaks = breakSet(numeral(0) + Z(1))
        , .zeros  = breakSet(numeral(0) + Z(1))
        },
        { .term = x - floor(x) - a
        , .breaks = breakSet(numeral(0) + Z(1))
        , .zeros  = breakSet(        a  + Z(1))
        },
        { .term = x - floor(x) - frac(0,5)
        , .breaks = breakSet(numeral(0)   + Z(1))
        , .zeros  = breakSet(  frac(0,5)  + Z(1))
        },
        { .term = x - frac(1,2) * floor(2 * x) - a
        , .breaks = breakSet(numeral(0)   + Z(1,2))
        , .zeros  = breakSet(        a    + Z(1,2))
        },
        { .term = 2 * x - floor(2 * x) - a
        , .breaks = breakSet(numeral(0)    + Z(1,2))
        , .zeros  = breakSet(frac(1,2) * a + Z(1,2))
        },
        { .term = 2 * x - floor(2 * x + b) - a
        , .breaks = breakSet(-frac(1,2) * b + Z(1,2))
        , .zeros  = breakSet(frac(1,2) * a + Z(1,2))
        },
        { .term = x + floor(x - a) + floor(-2 * x + 2 * b)
        , .breaks = breakSet(a + Z(1), b + Z(1,2))
        , .zeros  = breakSet( 1 + floor(2 * a + -2 * b) + Z(1)
                            , 1 - floor(-a + b) + Z(1,2) )
        },
      };
      for (auto t : lira_tests) {


        DEF_TEST(non_linear_case_1, 
            TermAnalysisTest {
              .term =  t.term,
              .expected = allPass( TEST_CMP(result.oslp, ==, 0)
                                 , TEST_CMP(result.sslp, > , 0)
                                 , TEST_CMP(result.breaks, ==,  t.breaks)
                                 )
            })


        DEF_TEST(non_linear_case_1, 
            TermAnalysisTest {
              .term =  -t.term,
              .expected = allPass( TEST_CMP(result.oslp, ==, 0)
                                 , TEST_CMP(result.sslp, < , 0)
                                 , TEST_CMP(result.breaks, ==,  t.breaks)
                                 )
            })


        DEF_TEST(non_linear_case_1_pos_sslp_gt, 
            ElimSetTest {
              .conj = { t.term > 0 }, 
              .expected = set_equal( 
                  iter::concat( plus_epsilon(t.breaks)
                              , plus_epsilon(t.zeros) 
                              , vt(t.breaks)) 
                  | iter::collect_vec
               ), 
            })

        // >=

        DEF_TEST(non_linear_case_1_pos_sslp_geq,
            ElimSetTest {
              .conj = { t.term >= 0 }, 
              .expected = set_equal( 
                  iter::concat( plus_epsilon(t.breaks)
                              , vt(t.zeros) 
                              , vt(t.breaks)) 
                  | iter::collect_vec
               ), 
            })

        DEF_TEST(non_linear_case_1_neg_sslp_geq,
            ElimSetTest {
              .conj = { -t.term >= 0 }, 
              .expected = set_equal( 
                  iter::concat( plus_epsilon(t.breaks)
                              , vt(t.breaks)
                              ) 
                  | iter::collect_vec
               ), 
            })

        // > 
        DEF_TEST(non_linear_case_1_pos_sslp_gt,
            ElimSetTest {
              .conj = { t.term > 0 }, 
              .expected = set_equal( 
                  iter::concat( plus_epsilon(t.breaks)
                              , plus_epsilon(t.zeros) 
                              , vt(t.breaks)
                              ) 
                  | iter::collect_vec
               ), 
            })



        DEF_TEST(non_linear_case_1_neg_sslp_gt,
            ElimSetTest {
              .conj = { -t.term > 0 }, 
              .expected = set_equal( 
                  iter::concat( plus_epsilon(t.breaks)
                              , vt(t.breaks)
                              ) 
                  | iter::collect_vec
               ), 
            })

        // ==

        DEF_TEST(non_linear_case_1_pos_sslp_eq,
            ElimSetTest {
              .conj = { eq(t.term, 0) }, 
              .expected = set_equal( 
                  iter::concat( vt(t.zeros)
                              , vt(t.breaks)) 
                  | iter::collect_vec
               ), 
            })


        DEF_TEST(non_linear_case_1_neg_sslp_eq,
            ElimSetTest {
              .conj = { eq(-t.term, 0) }, 
              .expected = set_equal( 
                  iter::concat( vt(t.zeros)
                              , vt(t.breaks)) 
                  | iter::collect_vec
               ), 
            })


        // !=

        DEF_TEST(non_linear_case_1_pos_sslp_neq,
            ElimSetTest {
              .conj = { neq(t.term, 0) }, 
              .expected = set_equal( 
                  iter::concat( plus_epsilon(t.breaks)
                              , plus_epsilon(t.zeros)
                              , vt(t.breaks)) 
                  | iter::collect_vec
               ), 
            })


        DEF_TEST(non_linear_case_1_neg_sslp_neq,
            ElimSetTest {
              .conj = { neq(-t.term, 0) }, 
              .expected = set_equal( 
                  iter::concat( plus_epsilon(t.breaks)
                              , plus_epsilon(t.zeros)
                              , vt(t.breaks)) 
                  | iter::collect_vec
               ), 
            })

      }

    }

    {
      struct PeriodicZeroSlopeTermTest {
        Term<C> term;
        std::vector<Break<C>> breaks;
      };
      std::vector<PeriodicZeroSlopeTermTest> lira_tests = {
        { .term = floor(x) - floor(x - a),
          .breaks = breakSet(numeral(0) + Z(1), a + Z(1)), },

        { .term = frac(1,2) * x + floor(x) + x - floor(x - a) - frac(3,2) * x,
          .breaks = breakSet(numeral(0) + Z(1), a + Z(1)), },

        { .term = 2 * floor(frac(1,2) * x) - floor(x - a),
          .breaks = breakSet(numeral(0) + Z(2), a + Z(1)), },

        { .term = b + floor(x) - floor(x - a),
          .breaks = breakSet(numeral(0) + Z(1), a + Z(1)), },

        { .term = floor(3 * (x - a)) - floor(x - b) - floor(2 * (x - c)),
          .breaks = breakSet(a + Z(1,3), b + Z(1), c + Z(1,2)), },

      };

      for (auto& t : lira_tests) {

        DEF_TEST(non_linear_case_2, 
            TermAnalysisTest {
              .term =  t.term,
              .expected = allPass( TEST_CMP(result.oslp, ==, 0)
                                 , TEST_CMP(result.sslp, ==, 0)
                                 , TEST_F(is_set_equal, result.breaks, t.breaks)
                                 )
            })


        DEF_TEST(non_linear_case_2_eq, 
            ElimSetTest {
              .conj = { t.term > 0 }, 
              .expected = set_equal( 
                  iter::concat( plus_epsilon(t.breaks)
                              , vt(t.breaks)) 
                  | iter::collect_vec
               ), 
            })



      }
    }


    // TODO aperiodic tests systematically testing all cases

    //////////////////////////////////////////////////////////////////////////////////////
    // term property tests
    //////////////////////////////////////////////////////////////////////////////////////

    DEF_TEST(props_0,
        TermAnalysisTest {
          .term     = floor( x ) - 1,
          .expected =  allPass(
                TEST_EQ(result.distYminus, term(-2))
              , TEST_EQ(result.distXminus(), term(1))
              ),
        })

    DEF_TEST(props_1,
        TermAnalysisTest {
          .term     = term(1),
          .expected =  allPass(
              TEST_EQ(result.distYminus, term(1))
              ),
        })

    DEF_TEST(props_2,
        TermAnalysisTest {
          .term     = term(-numeral(1)),
          .expected =  allPass(TEST_EQ(result.distYminus, term(-1))),
        })

    DEF_TEST(props_3,
        TermAnalysisTest {
          .term     = x,
          .expected =  allPass(
                TEST_EQ(result.distYminus, term(0))
              , TEST_EQ(result.distXminus(), term(0))
              ),
        })

    DEF_TEST(props_4,
        TermAnalysisTest {
          .term     = floor(x),
          .expected =  allPass(
                TEST_EQ(result.distYminus, term(-1))
              , TEST_EQ(result.oslp, numeral(1))
              , TEST_EQ(result.distXminus(), term(0))
              ),
        })


    DEF_TEST(props_5_a,
        TermAnalysisTest {
          .term     = floor(x),
          .expected =  allPass(
                TEST_EQ(result.distXminus(), term(0))
              , TEST_EQ(result.deltaX(), numeral(1))
              ),
        })


    DEF_TEST(props_5_b,
        TermAnalysisTest {
          .term     = 2 * floor(x),
          .expected =  allPass(
                TEST_EQ(result.distXminus(), term(0))
              , TEST_EQ(result.deltaX(), numeral(1))
              ),
        })

    DEF_TEST(props_5_c,
        TermAnalysisTest {
          .term     = frac(1,2) * floor(x),
          .expected =  allPass(
                TEST_EQ(result.distXminus(), term(0))
              , TEST_EQ(result.deltaX(), numeral(1))
              ),
        })


    return tests;
  }

};

template<class Api>
auto viras_test(Api api)
{ return VirasTest<Config<Api, DefaultOpts>>(Config<Api, DefaultOpts>(std::move(api), DefaultOpts() )); }



} // namespace viras
