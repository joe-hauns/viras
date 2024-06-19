
#define DERIVE_TUPLE(Slf,...)                                                             \
      using Self = Slf;                                                                   \
      auto asTuple() const { return std::tie(__VA_ARGS__); }                              \

#define DERIVE_TUPLE_EQ                                                                   \
      friend bool operator==(Self const& lhs, Self const& rhs)                            \
      { return lhs.asTuple() == rhs.asTuple(); }                                          \

#define DERIVE_TUPLE_LESS                                                                 \
      friend bool operator<(Self const& lhs, Self const& rhs)                             \
      { return lhs.asTuple() < rhs.asTuple(); }                                           \


