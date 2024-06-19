#pragma once
#include "viras.h"
#include <regex>
#include <sstream>

namespace viras {

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


// TODO move to viras/lib.h
template<class... Ts> 
std::string output_to_string(Ts const&... ts)
{ 
  std::stringstream out;
  (out << ... << ts);
  return out.str();
}

template<class Config>
struct VirasTest : Viras<Config> {

  template<class... As>
  VirasTest(As... as) : Viras<Config>(as...) {}

  using VirtualTerm = typename Viras<Config>::VirtualTerm;
  using Literal     = typename Viras<Config>::Literal;
  using Literals    = typename Viras<Config>::Literals;
  using Term        = typename Viras<Config>::Term;
  using LiraTerm    = typename Viras<Config>::LiraTerm;
  using Var         = typename Viras<Config>::Var;
  using Numeral     = typename Viras<Config>::Numeral;
  using Break       = typename Viras<Config>::Break;
  using Viras<Config>::epsilon;
  using Viras<Config>::Z;
  using Viras<Config>::infty;
  using Viras<Config>::term;
  using Viras<Config>::numeral;

  public:

  struct AllContained {
    std::vector<VirtualTerm> expected;

    std::optional<std::string> check(std::vector<VirtualTerm> const& result) {
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


  struct ExpectedCheck : std::variant<AllContained> 
  {
    using std::variant<AllContained>::variant;
    std::optional<std::string> check(std::vector<VirtualTerm> const& result) 
    { return std::visit([&](auto& x) { return x.check(result); }, *this); }
    friend std::ostream& operator<<(std::ostream& out, ExpectedCheck const& self)
    { std::visit([&](auto& self) { out << self; }, self); return out; }
  };

  template<class... As>
  ExpectedCheck containsAll(As... as)
  { return ExpectedCheck(AllContained{std::vector<VirtualTerm>{VirtualTerm(as)...}}); }


  struct ElimSetTest {
    Var x;
    std::vector<Literal> conj;
    ExpectedCheck expected;

    template<class C>
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
    using TestFun = std::function<std::optional<std::string>(Term, LiraTerm&)>;
    Var x;
    Term term;
    std::vector<TestFun> expected;

    template<class C>
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

  void run_tests(std::regex regex) {
    for (auto& testCase : tests()) {
      if (std::regex_match(testCase.first, regex)) {
        run_test(testCase);
      }
    }
  }

  auto run_tests(const char* regex) { return run_tests(std::basic_regex(regex)); }
  auto run_test (const char* test)  { return run_test(std::string(test)); }

  void run_test(std::string const& name){
    for (auto& testCase : tests()) {
      if (testCase.first == name) {
        run_test(testCase);
      }
    }
  }


  void auto_test(){
    if (std::getenv("VIRAS_TEST_NAME")) {
      run_test(std::getenv("VIRAS_TEST_NAME"));
    } else if (std::getenv("VIRAS_TEST_PATTERN")) {
      run_tests(std::getenv("VIRAS_TEST_PATTERN"));
    } else {
      run_tests(".*");
    }
  }

  template<class... As>
  auto breakSet(As... as)
  { return std::vector<Break> { Break{ *as.term, *as.period }... }; }


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

#define DEF_TEST(name, ...)                                                               \
    {                                                                                     \
      auto test = __VA_ARGS__;                                                            \
      test.x = x_var;                                                                     \
      tests.push_back(std::make_pair(#name, std::move(test)));                            \
    }                                                                                     \

#define TEST_EQ(lhs, rhs)                                                                 \
  [=](auto input, LiraTerm& result) -> std::optional<std::string> {                       \
    if(lhs == rhs)  {                                                                     \
      return std::optional<std::string>();                                                \
    } else {                                                                              \
      return output_to_string(                                                  \
          "[    input ] ", input, "\n",                                       \
          "[    query ] ", #lhs, "\n",                                        \
          "[    value ] ", lhs, "\n",                                         \
          "[ expected ] ", rhs, "\n"                                          \
          );                                                                       \
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
          .conj = { eq(floor(x), x) },
          .expected = containsAll( 0 + Z(1), term(0) + epsilon + Z(1) ),  // TODO do we really need eps and non-eps here
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

} // namespace viras
