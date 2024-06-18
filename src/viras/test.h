#pragma once
#include "viras.h"

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


  // TODO use this instead of outputToString
  // template<class... As>
  // std::string output_to_string(As const&... as) 
  // { std::string_stream;  }

#define pretty(...) __VA_ARGS__
template<class Config>
struct VirasTest : Viras<Config> {

  template<class... As>
  VirasTest(As... as) : Viras<Config>(as...) {}

  using VirtualTerm = typename Viras<Config>::VirtualTerm;
  using Literal     = typename Viras<Config>::Literal;
  using Literals    = typename Viras<Config>::Literals;
  using Term        = typename Viras<Config>::Term;
  using CTerm       = typename Viras<Config>::CTerm;
  using LiraTerm    = typename Viras<Config>::LiraTerm;
  using Var         = typename Viras<Config>::Var;
  using Numeral     = typename Viras<Config>::Numeral;
  using CNumeral    = typename Viras<Config>::CNumeral;
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
        // if (!arrayIter(result).any([&](auto& res) { return eqModAC(res, s); }) ) {
          return string(outputToString("not found: ", s));
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
    void run(Viras<C>& viras)
    {
      auto analysed = iter::array(conj) 
        | iter::map([&](auto l) { return viras.analyse(*l, x); })
        | iter::collect_vec;
      auto result = viras.elim_set(x, analysed) | iter::collect_vec;
      auto simpl = SimplifyingConfig<C>(viras._config);
      // auto simplResult = iter::array(result)
      //       | iter::map([&](auto t) { return simpl.simpl(t); })
      //       | iter::collect_vec;
      auto error = expected.check(result);
      if (error) {
        std::cout << "[     FAIL ] " << conj << std::endl;
        std::cout << "[   result ] " << result << std::endl;
        std::cout << "[    error ] " << *error << std::endl;
        std::cout << "[ expected ] " <<    expected << std::endl;
      } else {
        std::cout << "[     OK   ] " << conj << std::endl;

      }
      assert(!error);
      // if (error) {
      //     std::cout << "[         case ] " << pretty(     conj ) << std::endl;
      //     std::cout << "[       result ] " << pretty(      result ) << std::endl;
      //     // std::cout << "[ simpl result ] " << pretty( simplResult ) << std::endl;
      //     std::cout << "[        error ] " << pretty(      *error ) << std::endl;
      //     std::cout << "[     expected ] " << pretty(    expected ) << std::endl;
      //     exit(-1);
      // }
    }
  };


  struct TermAnalysisTest {
    using TestFun = std::function<void(Term, LiraTerm&)>;
    Var x;
    Term term;
    std::vector<TestFun> expected;

    template<class C>
    void run(Viras<C>& viras)
    {
      auto result = viras.analyse(term, x);
      for (auto& c : expected) {
        c(term, result);
      }
    }
  };

  using Test = std::variant<ElimSetTest, TermAnalysisTest>;

template<class... Ts>
struct overloaded : Ts... { using Ts::operator()...; };

template<class... Ts>
overloaded(Ts...) -> overloaded<Ts...>;

  void run_tests(){
    for (auto [name, test] : tests()) {
      std::visit([&](auto& test) { test.run(*this); }, test);
      // std::cout << "[ TEST ] " << name;
    }
  }

  // template<class A, class... As>
  // static std::vector<Literal> conj(A a, As... as) {
  //
  //   return std::vector<Literal>();
  // }
  //
  // static std::vector<Literal> conj() {
  //   return std::vector<Literal>();
  // }

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

    // auto conj = [](auto... args) { 
    //   std::vector<Literal> out;
    //   (out.push_back(args)...);
    //   return out;
    // };


#define DEF_TEST(name, ...)                                                               \
    {                                                                                     \
      auto test = __VA_ARGS__;                                                            \
      test.x = x_var;                                                                     \
      tests.push_back(std::make_pair(#name, std::move(test)));                            \
    }                                                                                     \

#define TEST_EQ(lhs, rhs)                                                                 \
  [&](auto input, LiraTerm& result) {                                                     \
    ASS(lhs == rhs)                                                                       \
  }

  //   if (lhs != rhs) {                                             
  //     std::cout << "[         case ] " << pretty(      input ) << std::endl;              
  //     std::cout << "[       result ] " << pretty(     result ) << std::endl;              
  //     std::cout << "[        check ] " << #lhs << " == " << pretty( rhs ) << std::endl;   
  //     std::cout << "[       result ] " << pretty( lhs ) << std::endl; 
  //     exit(-1);                                                                           
  //   }                                                                                     
  // }                                                                                       


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
          .conj = { eq(floor(x - frac(1,2)), x) },
          .expected = containsAll( frac(1,2) + Z(1) ), 
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
          // , x - 2 * floor(frac(1,2) * x) - b > 0
          // , floor(3 * x - c) + floor(-3 * x + c) == 0
          },
          .expected = containsAll( term(1) ), 
        })

    DEF_TEST(motivating_test_3,
        ElimSetTest {
          .conj = { 
            floor( x ) - 1 > 0
          // , x - 2 * floor(frac(1,2) * x) - b > 0
          // , floor(3 * x - c) + floor(-3 * x + c) == 0
          },
          .expected = containsAll( term(2) ), 
        })

    DEF_TEST(motivating_test_4,
        ElimSetTest {
          .conj = { 
            -floor( -x ) - 1 > 0
          // , x - 2 * floor(frac(1,2) * x) - b > 0
          },
          .expected = containsAll( numeral(1) + epsilon ), 
        })

    DEF_TEST(motivating_test_5,
        ElimSetTest {
          .conj = { 
            eq(-floor( -x ) - 1, 0)
          // , x - 2 * floor(frac(1,2) * x) - b > 0
          },
          .expected = containsAll( numeral(1) ), 
        })

    DEF_TEST(motivating_test_2,
        ElimSetTest {
          .conj = { 
            floor( x ) - a >= 0
          // , x - 2 * floor(frac(1,2) * x) - b > 0
          },
          .expected = containsAll( -floor(-a),  -floor(-a) + epsilon ), 
        })

     
      // - k: -1
      //   d: 1
      //   floors: 
      //   - { k: 1, l:  1, d: 0 }
      //   # - { k: 1, l: -1, d: 0 }
      //   color: blue
      //   relation: Geq
      //
      //
      // - k: 1
      //   d: 3
      //   floors: 
      //   color: red
      //   relation: Geq
      //
      //
      // - k: -2
      //   d: 3
      //   floors: 
      //   color: orange
      //   relation: Eq

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
          // .expected = allPass(TEST_EQ(result.lim, -x + floor(x) + 1))
        })

    DEF_TEST(some_props_2, 
        TermAnalysisTest {
          .term = floor(2 * (-floor(-3 * x + a) - x) - b),
          .expected = allPass( 
                               TEST_EQ(result.breaks,  breakSet( frac(1,3) * a + Z(1,3)))
                             , TEST_EQ(result.per,     frac(1,3))
                             )
          // .expected = allPass(TEST_EQ(result.lim, -x + floor(x) + 1))
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
          .expected = containsAll( a + Z(1) ), 
        })


    // DEF_TEST(motivating, 
    //     ElimSetTest {
    //       .conj = { 
    //          floor( x ) - a >= 0
    //       ,  -x     >= 0
    //       , x - 2 * floor(frac(1,2) * x) - 1 > 0
    //       },
    //       .expected = containsAll( a + Z(1) ), 
    //     })

    // DEF_TEST(motivating, 
    //     ElimSetTest {
    //       .conj = { 
    //         floor( x ) - a >= 0
    //       , x - 2 * floor(frac(1,2) * x) - b > 0
    //       },
    //       .expected = containsAll( a + Z(1) ), 
    //     })

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
                // TEST_EQ(result.distYminus, term(-1))
              // , TEST_EQ(result.oslp, numeral(1))
                TEST_EQ(result.distXminus(), term(0))
              , TEST_EQ(result.deltaX(), numeral(1))
              ),
        })


    DEF_TEST(props_5_b,
        TermAnalysisTest {
          .term     = 2 * floor(x),
          .expected =  allPass(
                // TEST_EQ(result.distYminus, term(-1))
              // , TEST_EQ(result.oslp, numeral(1))
                TEST_EQ(result.distXminus(), term(0))
              , TEST_EQ(result.deltaX(), numeral(1))
              ),
        })

    DEF_TEST(props_5_c,
        TermAnalysisTest {
          .term     = frac(1,2) * floor(x),
          .expected =  allPass(
                // TEST_EQ(result.distYminus, term(-1))
              // , TEST_EQ(result.oslp, numeral(1))
                TEST_EQ(result.distXminus(), term(0))
              , TEST_EQ(result.deltaX(), numeral(1))
              ),
        })

    return tests;
  }

};



};
#undef pretty
