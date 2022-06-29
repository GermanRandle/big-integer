#pragma once

#include <iosfwd>
#include <string>
#include <cstdint>
#include <vector>
#include <functional>

struct big_integer {
  big_integer();
  big_integer(big_integer const& other);
  big_integer(int a);
  big_integer(unsigned int a);
  big_integer(long a);
  big_integer(unsigned long a);
  big_integer(long long a);
  big_integer(unsigned long long a);
  explicit big_integer(std::string const& str);
  ~big_integer();

  big_integer& operator=(big_integer const& other);

  big_integer& operator+=(big_integer const& rhs);
  big_integer& operator-=(big_integer const& rhs);
  big_integer& operator*=(big_integer const& rhs);
  big_integer& operator/=(big_integer const& rhs);
  big_integer& operator%=(big_integer const& rhs);

  big_integer& operator&=(big_integer const& rhs);
  big_integer& operator|=(big_integer const& rhs);
  big_integer& operator^=(big_integer const& rhs);

  big_integer& operator<<=(int rhs);
  big_integer& operator>>=(int rhs);

  big_integer operator+() const;
  big_integer operator-() const;
  big_integer operator~() const;

  big_integer& operator++();
  big_integer operator++(int);

  big_integer& operator--();
  big_integer operator--(int);

  friend bool operator==(big_integer const& a, big_integer const& b);
  friend bool operator!=(big_integer const& a, big_integer const& b);
  friend bool operator<(big_integer const& a, big_integer const& b);
  friend bool operator>(big_integer const& a, big_integer const& b);
  friend bool operator<=(big_integer const& a, big_integer const& b);
  friend bool operator>=(big_integer const& a, big_integer const& b);

  friend std::string to_string(big_integer const& a);

private:

  std::vector<uint32_t> digits_;

  void ull_constructor_(unsigned long long a);
  void inplace_negate_();
  bool is_negative_() const;
  bool is_zero_() const;
  uint32_t get_addition_() const;
  void add_digit_(uint32_t dig, size_t start_pos, bool shrink);
  void mul_digit_(uint32_t dig, bool shrink);
  uint32_t div_digit_(uint32_t dig, bool shrink);
  void remove_leading_digits_();
  void reserve_(size_t new_size, uint32_t filler);
  big_integer& bitwise_operation_(std::function<uint32_t(uint32_t, uint32_t)> const &lambda, big_integer const& rhs);

  static uint32_t trial_for_div_(big_integer const & r, big_integer const & d, size_t k, size_t m);
  static bool smaller_for_div_(big_integer const & r, big_integer const & dq, size_t k, size_t m);
  static void difference_for_div_(big_integer& r, big_integer const& dq, size_t k, size_t m);
  static std::pair<big_integer, big_integer> long_divide_(big_integer const& x, big_integer const& y, size_t n, size_t m);
  big_integer& divmod(big_integer const& rhs, bool div);
};

big_integer operator+(big_integer a, big_integer const& b);
big_integer operator-(big_integer a, big_integer const& b);
big_integer operator*(big_integer a, big_integer const& b);
big_integer operator/(big_integer a, big_integer const& b);
big_integer operator%(big_integer a, big_integer const& b);

big_integer operator&(big_integer a, big_integer const& b);
big_integer operator|(big_integer a, big_integer const& b);
big_integer operator^(big_integer a, big_integer const& b);

big_integer operator<<(big_integer a, int b);
big_integer operator>>(big_integer a, int b);

bool operator==(big_integer const& a, big_integer const& b);
bool operator!=(big_integer const& a, big_integer const& b);
bool operator<(big_integer const& a, big_integer const& b);
bool operator>(big_integer const& a, big_integer const& b);
bool operator<=(big_integer const& a, big_integer const& b);
bool operator>=(big_integer const& a, big_integer const& b);

std::string to_string(big_integer const& a);
std::ostream& operator<<(std::ostream& s, big_integer const& a);
