#include "big_integer.h"
#include <cstddef>
#include <cstring>
#include <ostream>
#include <stdexcept>
#include <utility>
#include <cassert>
#include <algorithm>
#include <limits>

static uint32_t const LEADING_BIT = 0x80000000u;
static uint64_t const BASE = (1ull << 32);
static uint32_t const UINT_1E9 = 1000000000;

static bool is_neg_digit(uint32_t dig) {
  return (dig & LEADING_BIT) != 0;
}

static std::pair<uint32_t, uint32_t> uadd_overflow(uint32_t a, uint32_t b) {
  uint64_t result = static_cast<uint64_t>(a) + static_cast<uint64_t>(b);
  return {result & static_cast<uint64_t>(UINT32_MAX), result >= BASE};
}

static std::pair<uint32_t, uint32_t> usub_overflow(uint32_t a, uint32_t b) {
  int64_t result = static_cast<int64_t>(a) - static_cast<int64_t>(b);
  if (result < 0) {
    return {static_cast<uint32_t>(result + BASE), 1};
  }
  return {static_cast<uint32_t>(result), 0};
}

bool big_integer::is_zero_() const {
  return digits_.empty();
}

bool big_integer::is_negative_() const {
  return !digits_.empty() && is_neg_digit(digits_.back());
}

void big_integer::inplace_negate_() {
  if (is_zero_()) {
    return;
  }
  for (uint32_t & digit : digits_) {
    digit = ~digit;
  }
  add_digit_(1, 0, true);
}

uint32_t big_integer::get_addition_() const {
  return is_negative_() ? UINT32_MAX : 0;
}

void big_integer::reserve_(size_t new_size, uint32_t filler) {
  digits_.reserve(new_size);
  for (size_t i = digits_.size(); i < new_size; i++) {
    digits_.push_back(filler);
  }
}

void big_integer::add_digit_(uint32_t dig, size_t start_pos, bool shrink) {
  if (is_zero_()) {
    digits_.push_back(dig);
    if (!is_negative_()) {
      digits_.push_back(0);
    }
    remove_leading_digits_();
    return;
  }
  bool init_sign = is_negative_();
  for (size_t i = start_pos; i < digits_.size() && dig != 0; i++) {
    auto temp = uadd_overflow(digits_[i], dig);
    digits_[i] = temp.first;
    dig = temp.second;
  }
  if (!init_sign) {
    digits_.push_back(dig);
  }
  if (shrink) {
    remove_leading_digits_();
  }
}

void big_integer::mul_digit_(uint32_t dig, bool shrink) {
  assert(!is_negative_());
  uint64_t carry = 0;
  for (uint32_t & cur : digits_) {
    uint64_t temp = static_cast<uint64_t>(cur) * static_cast<uint64_t>(dig) + carry;
    cur = static_cast<uint32_t>(temp % BASE);
    carry = static_cast<uint32_t>(temp / BASE);
  }
  if (carry > 0) {
    digits_.push_back(carry);
  }
  if (is_negative_()) {
    digits_.push_back(0);
  } else if (shrink) {
    remove_leading_digits_();
  }
}

uint32_t big_integer::div_digit_(uint32_t dig, bool shrink) {
  assert(!is_negative_());
  uint64_t remainder = 0;
  for (size_t i = digits_.size(); i > 0; i--) {
    uint64_t temp = static_cast<uint64_t>(remainder) * BASE + static_cast<uint64_t>(digits_[i - 1]);
    digits_[i - 1] = static_cast<uint32_t>(temp / static_cast<uint64_t>(dig));
    remainder = temp % static_cast<uint64_t>(dig);
  }
  if (shrink) {
    remove_leading_digits_();
  }
  return remainder;
}

void big_integer::remove_leading_digits_() {
  while (digits_.size() > 1 && ((digits_.back() == 0 && !is_neg_digit(digits_[digits_.size() - 2])) ||
                                (digits_.back() == UINT32_MAX && is_neg_digit(digits_[digits_.size() - 2])))) {
    digits_.pop_back();
  }
  if (digits_.size() == 1 && digits_[0] == 0) {
    digits_.pop_back();
  }
}

big_integer::big_integer() = default;

big_integer::big_integer(big_integer const& other) = default;

big_integer::big_integer(int a) : big_integer(static_cast<long long>(a)) {}

big_integer::big_integer(unsigned int a) : big_integer(static_cast<unsigned long long>(a)) {}

big_integer::big_integer(long a) : big_integer(static_cast<long long>(a)) {}

big_integer::big_integer(unsigned long a) : big_integer(static_cast<unsigned long long>(a)) {}

void big_integer::ull_constructor_(unsigned long long a) {
  while (a > 0) {
    digits_.push_back(a % BASE);
    a /= BASE;
  }
  if (is_negative_()) {
    digits_.push_back(0);
  }
}

big_integer::big_integer(long long a) {
  if (a >= 0) {
    ull_constructor_(static_cast<unsigned long long>(a));
  } else {
    if (a != std::numeric_limits<long long>::min()) {
      ull_constructor_(static_cast<unsigned long long>(-a));
      inplace_negate_();
    } else {
      ull_constructor_(static_cast<unsigned long long>(-(a + 1)));
      inplace_negate_();
      --(*this);
    }
  }
}

big_integer::big_integer(unsigned long long a) {
  ull_constructor_(a);
}

static uint32_t pow10(uint32_t exp) {
  if (exp == 1) {
    return 10;
  }
  uint32_t half = pow10(exp / 2);
  return half * half * (exp % 2 == 1 ? 10 : 1);
}

static void check_stoi(std::string const& str) {
  for (char c : str) {
    if (c < '0' || c > '9') {
      throw std::invalid_argument("String contains non-digit symbol");
    }
  }
}

big_integer::big_integer(std::string const& str) {
  if (str.empty() || str == "-") {
    throw std::invalid_argument("Invalid string");
  }
  bool neg_flag = (str[0] == '-');
  for (size_t i = neg_flag; i < str.size(); i += 9) {
    std::string part = str.substr(i, 9);
    check_stoi(part);
    uint32_t part_int = stoi(part);
    mul_digit_(pow10(part.length()), true);
    add_digit_(part_int, 0, true);
  }
  if (neg_flag) {
    inplace_negate_();
  }
}

big_integer::~big_integer() = default;

big_integer& big_integer::operator=(big_integer const& other) = default;

big_integer& big_integer::operator+=(big_integer const& rhs) {
  uint32_t carry = 0;
  uint32_t signsum = static_cast<uint32_t>(is_negative_()) + static_cast<uint32_t>(rhs.is_negative_());
  reserve_(rhs.digits_.size(), get_addition_());
  for (size_t i = 0; i < digits_.size(); i++) {
    uint32_t operand = (rhs.digits_.size() > i ? rhs.digits_[i] : rhs.get_addition_());
    auto temp = uadd_overflow(digits_[i], operand);
    auto res = uadd_overflow(temp.first, carry);
    res.second += temp.second;
    digits_[i] = res.first;
    carry = res.second;
  }
  if (signsum == 0 && is_negative_()) {
    digits_.push_back(0);
  } else if (signsum == 2) {
    digits_.push_back(UINT32_MAX);
  }
  remove_leading_digits_();
  return *this;
}

big_integer& big_integer::operator-=(big_integer const& rhs) {
  uint32_t borrow = 0;
  reserve_(rhs.digits_.size() + 1, get_addition_());
  for (size_t i = 0; i < digits_.size(); i++) {
    uint32_t operand = (rhs.digits_.size() > i ? rhs.digits_[i] : rhs.get_addition_());
    auto temp = usub_overflow(digits_[i], operand);
    auto res = usub_overflow(temp.first, borrow);
    res.second += temp.second;
    digits_[i] = res.first;
    borrow = res.second;
  }
  if (borrow && digits_.back() != 0) {
    digits_.push_back(UINT32_MAX);
  }
  remove_leading_digits_();
  return *this;
}

big_integer& big_integer::operator*=(big_integer const& rhs) {
  bool result_sign = is_negative_() ^ rhs.is_negative_();
  big_integer copy = rhs;
  if (is_negative_()) {
    inplace_negate_();
  }
  if (copy.is_negative_()) {
    copy.inplace_negate_();
  }

  big_integer result;
  result.reserve_(digits_.size() + copy.digits_.size() + 2, 0);
  for (size_t i = 0; i < digits_.size(); i++) {
    for (size_t j = 0; j < copy.digits_.size(); j++) {
      uint64_t temp = static_cast<uint64_t>(digits_[i]) * static_cast<uint64_t>(copy.digits_[j]);
      result.add_digit_(static_cast<uint32_t>(temp % BASE), i + j, false);
      result.add_digit_(static_cast<uint32_t>(temp / BASE), i + j + 1, false);
    }
  }

  result.remove_leading_digits_();
  if (result_sign) {
    result.inplace_negate_();
  }
  *this = result;
  return *this;
}

uint32_t big_integer::trial_for_div_(big_integer const& r, big_integer const& d, size_t k, size_t m) {
  uint64_t r2 = (static_cast<uint64_t>(r.digits_[k + m]) << 32) + static_cast<uint64_t>(r.digits_[k + m - 1]);
  return static_cast<uint32_t>(std::min(r2 / static_cast<uint64_t>(d.digits_[m - 1]), BASE - 1));
}

bool big_integer::smaller_for_div_(big_integer const& r, big_integer const& dq, size_t k, size_t m) {
  size_t i = m;
  size_t j = 0;
  while (i != j) {
    if (r.digits_[i + k] != dq.digits_[i]) {
      j = i;
    } else {
      i--;
    }
  }
  return r.digits_[i + k] < dq.digits_[i];
}

void big_integer::difference_for_div_(big_integer& r, big_integer const& dq, size_t k, size_t m) {
  uint64_t borrow = 0;
  for (size_t i = 0; i <= m; i++) {
    uint64_t diff = static_cast<uint64_t>(r.digits_[i + k]) -
                    static_cast<uint64_t>(dq.digits_[i]) - borrow + BASE;
    r.digits_[i + k] = static_cast<uint32_t>(diff % BASE);
    borrow = 1 - diff / BASE;
  }
}

std::pair<big_integer, big_integer> big_integer::long_divide_(big_integer const& x, big_integer const& y, size_t n, size_t m) {
  uint32_t f = 1;
  if (y.digits_[m - 1] != ~0u) {
    f = BASE / (y.digits_[m - 1] + 1);
  }
  big_integer r = x;
  r.mul_digit_(f, false);
  big_integer d = y;
  d.mul_digit_(f, false);
  big_integer q;
  q.reserve_(n - m + 1, 0);
  for (size_t k = n - m + 1; k > 0; k--) {
    uint32_t qt = trial_for_div_(r, d, k - 1, m);
    big_integer dq = d;
    dq.mul_digit_(qt, false);
    while (smaller_for_div_(r, dq, k - 1, m)) {
      qt--;
      dq = d;
      dq.mul_digit_(qt, false);
    }
    q.digits_[k - 1] = qt;
    difference_for_div_(r, dq, k - 1, m);
  }
  r.div_digit_(f, false);
  return {q, r};
}

big_integer& big_integer::divmod(const big_integer& rhs, bool div) {
  if (rhs.is_zero_()) {
    throw std::invalid_argument("Division by zero");
  }
  bool init_sign = is_negative_();
  bool result_sign = is_negative_() ^ rhs.is_negative_();
  big_integer copy = rhs;
  if (is_negative_()) {
    inplace_negate_();
  }
  if (copy.is_negative_()) {
    copy.inplace_negate_();
  }
  if (copy > *this) {
    if (div) {
      *this = 0;
    } else if (init_sign) {
      inplace_negate_();
    }
    return *this;
  }
  size_t m = copy.digits_.size() - (copy.digits_.back() == 0);
  if (m == 1) {
    uint32_t rem = div_digit_(copy.digits_[0], true);
    if (!div) {
      *this = rem;
    }
  } else {
    size_t n = digits_.size() - (digits_.back() == 0);
    digits_.push_back(0);
    auto [q, r] = long_divide_(*this, copy, n, m);
    std::swap(*this, (div? q : r));
  }
  if ((div && result_sign) || (!div && init_sign)) {
    inplace_negate_();
  } else {
    remove_leading_digits_();
  }
  return *this;
}

big_integer& big_integer::operator/=(big_integer const& rhs) {
  return divmod(rhs, true);
}

big_integer& big_integer::operator%=(big_integer const& rhs) {
  return divmod(rhs, false);
}

big_integer& big_integer::bitwise_operation_(std::function<uint32_t(uint32_t, uint32_t)> const &lambda, const big_integer& rhs) {
  reserve_(rhs.digits_.size(), get_addition_());
  for (size_t i = 0; i < digits_.size(); i++) {
    uint32_t operand = (rhs.digits_.size() > i ? rhs.digits_[i] : rhs.get_addition_());
    digits_[i] = lambda(digits_[i], operand);
  }
  remove_leading_digits_();
  return *this;
}

big_integer& big_integer::operator&=(big_integer const& rhs) {
  return bitwise_operation_([&](uint32_t x, uint32_t y){return x & y;}, rhs);
}

big_integer& big_integer::operator|=(big_integer const& rhs) {
  return bitwise_operation_([&](uint32_t x, uint32_t y){return x | y;}, rhs);
}

big_integer& big_integer::operator^=(big_integer const& rhs) {
  return bitwise_operation_([&](uint32_t x, uint32_t y){return x ^ y;}, rhs);
}

static uint32_t capture_bits_suff(uint32_t number, uint32_t amount) {
  auto mask = ((~0u) - static_cast<uint32_t>((1ull << (32 - amount)) - 1));
  return static_cast<uint32_t>(static_cast<uint64_t>(number & mask) >> (32 - amount));
}

static uint32_t capture_bits_pref(uint32_t number, uint32_t amount) {
  auto mask = static_cast<uint32_t>((1ull << amount) - 1);
  return static_cast<uint32_t>(static_cast<uint64_t>(number & mask) << (32 - amount));
}

static void replace_lower_bits(uint32_t& x, uint32_t bits, uint32_t cnt) {
  x -= static_cast<uint32_t>(static_cast<uint64_t>(x) % (1ull << cnt));
  x += bits;
}

static void replace_higher_bits(uint32_t& x, uint32_t bits, uint32_t cnt) {
  x &= static_cast<uint32_t>((1ull << (32 - cnt)) - 1);
  x += bits;
}

big_integer& big_integer::operator<<=(int rhs) {
  if (rhs < 0) {
    throw std::invalid_argument("Can't do negative shift");
  }
  size_t extend_cnt = (rhs + 31) / 32;
  reserve_(digits_.size() + extend_cnt, get_addition_());
  uint32_t take_suff = rhs % 32;
  uint32_t take_pref = 32 - take_suff;
  for (size_t i = digits_.size() - extend_cnt; i > 0; i--) {
    uint32_t higher = capture_bits_suff(digits_[i - 1], take_suff);
    uint32_t lower = capture_bits_pref(digits_[i - 1], take_pref);
    digits_[i - 1] = 0;
    replace_lower_bits(digits_[i - 1 + extend_cnt], higher, take_suff);
    replace_higher_bits(digits_[i - 2 + extend_cnt], lower, take_pref);
  }
  remove_leading_digits_();
  return *this;
}

big_integer& big_integer::operator>>=(int rhs) {
  if (rhs < 0) {
    throw std::invalid_argument("Can't do negative shift");
  }
  size_t compress_cnt = rhs / 32;
  if (compress_cnt > digits_.size()) {
    *this = 0;
    return *this;
  }
  uint32_t take_suff = 32 - rhs % 32;
  uint32_t take_pref = 32 - take_suff;
  bool init_sign = is_negative_();
  digits_.push_back(get_addition_());
  for (size_t i = compress_cnt; i < digits_.size(); i++) {
    uint32_t higher = capture_bits_suff(digits_[i], take_suff);
    uint32_t lower = capture_bits_pref(digits_[i], take_pref);
    digits_[i] = 0;
    digits_[i - compress_cnt] = higher;
    if (i > compress_cnt) {
      digits_[i - compress_cnt - 1] += lower;
    }
  }
  digits_.resize(digits_.size() - compress_cnt);
  if (take_suff != 32) {
      digits_.back() = (init_sign ? UINT32_MAX : 0);
  }
  remove_leading_digits_();
  return *this;
}

big_integer big_integer::operator+() const {
  return *this;
}

big_integer big_integer::operator-() const {
  big_integer copy = *this;
  copy.inplace_negate_();
  return copy;
}

big_integer big_integer::operator~() const {
  big_integer copy = *this;
  for (uint32_t & digit : copy.digits_) {
    digit = ~digit;
  }
  return copy;
}

big_integer& big_integer::operator++() {
  add_digit_(1, 0, true);
  return *this;
}

big_integer big_integer::operator++(int) {
  big_integer copy = *this;
  add_digit_(1, 0, true);
  return copy;
}

big_integer& big_integer::operator--() {
  if (is_zero_()) {
    digits_.push_back(UINT32_MAX);
    return *this;
  }
  for (size_t i = 0; i < digits_.size(); i++) {
    if (digits_[i] == 0) {
      digits_[i] = UINT32_MAX;
    } else {
      if (i + 1 == digits_.size() && digits_.back() == LEADING_BIT) {
        digits_.push_back(UINT32_MAX);
      }
      digits_[i]--;
      break;
    }
  }
  return *this;
}

big_integer big_integer::operator--(int) {
  big_integer copy = *this;
  --(*this);
  return copy;
}

big_integer operator+(big_integer a, big_integer const& b) {
  return a += b;
}

big_integer operator-(big_integer a, big_integer const& b) {
  return a -= b;
}

big_integer operator*(big_integer a, big_integer const& b) {
  return a *= b;
}

big_integer operator/(big_integer a, big_integer const& b) {
  return a /= b;
}

big_integer operator%(big_integer a, big_integer const& b) {
  return a %= b;
}

big_integer operator&(big_integer a, big_integer const& b) {
  return a &= b;
}

big_integer operator|(big_integer a, big_integer const& b) {
  return a |= b;
}

big_integer operator^(big_integer a, big_integer const& b) {
  return a ^= b;
}

big_integer operator<<(big_integer a, int b) {
  return a <<= b;
}

big_integer operator>>(big_integer a, int b) {
  return a >>= b;
}

bool operator==(big_integer const& a, big_integer const& b) {
  return a.digits_ == b.digits_;
}

bool operator!=(big_integer const& a, big_integer const& b) {
  return a.digits_ != b.digits_;
}

bool operator<(big_integer const& a, big_integer const& b) {
  if (a.is_negative_() ^ b.is_negative_()) {
    return a.is_negative_();
  }
  if (a.is_negative_() && a.digits_.size() != b.digits_.size()) {
    return a.digits_.size() > b.digits_.size();
  } else if (!a.is_negative_() && a.digits_.size() != b.digits_.size()) {
    return a.digits_.size() < b.digits_.size();
  }
  for (size_t i = a.digits_.size(); i > 0; i--) {
    if (a.digits_[i - 1] != b.digits_[i - 1]) {
      return a.digits_[i - 1] < b.digits_[i - 1];
    }
  }
  return false;
}

bool operator>(big_integer const& a, big_integer const& b) {
  return b < a;
}

bool operator<=(big_integer const& a, big_integer const& b) {
  return !(a > b);
}

bool operator>=(big_integer const& a, big_integer const& b) {
  return !(a < b);
}

std::string to_string(big_integer const& a) {
  std::string result;
  bool neg_flag = false;
  big_integer copy = a;
  if (copy.is_negative_()) {
    copy.inplace_negate_();
    neg_flag = true;
  }
  while (!copy.is_zero_()) {
    uint32_t rem = copy.div_digit_(UINT_1E9, true);
    std::string str_rem = std::to_string(rem);
    std::reverse(str_rem.begin(), str_rem.end());
    result += str_rem;
    if (!copy.is_zero_()) {
      for (size_t i = str_rem.size(); i < 9; i++) {
        result += '0';
      }
    }
  }
  if (neg_flag) {
    result += '-';
  }
  std::reverse(result.begin(), result.end());
  if (result.empty()) {
    result = "0";
  }
  return result;
}

std::ostream& operator<<(std::ostream& s, big_integer const& a) {
  return s << to_string(a);
}
