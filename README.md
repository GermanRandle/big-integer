# bigint
In this task, you are required to implement a class for a large signed integer.

## Implementation Requirements

The class should be called `big_integer`, and your solution code should be located in the files `big_integer.h` and `big_integer.cpp`.

You are expected to implement:
- A default constructor that initializes the number to zero.
- A copy constructor.
- Constructors from numeric types.
- An explicit constructor from `std::string`.
- Assignment operator.
- Comparison operators.
- Arithmetic operations: addition, subtraction, multiplication, division, unary minus, and plus.
- Increment and decrement operations.
- Bitwise operations: and, or, exclusive or, not (similar to bitwise operations for `int`).
- Bit shifts.
- An external function `std::string to_string(const big_integer&)`.

The implementation must meet the following criteria:
- Multiplication and division should not be worse than O(nm).
- Other operations should be conducted with the maximum possible asymptotic efficiency.
- Aside from asymptotic considerations, focus on minimizing the number of allocations and overall runtime.
- Digits of the number should be represented by at least 32-bit numbers, and all bits in their representation must be used.
- The use of external libraries in completing the task is prohibited.
- `big_integer` must be creatable from numeric types retaining the value. If a numeric variable had a value `x`, then `big_integer` after creation should have the value `x`.
- The time for passing tests in CI should not exceed 1 second in Release-build, and your solution should fit within the limit on each restart.

It might be helpful to refer to the book ["Modern Computer Arithmetic"](https://members.loria.fr/PZimmermann/mca/mca-0.5.pdf) and the article ["Multiple-Length Division Revisited: A Tour of the Minefield"](https://surface.syr.edu/cgi/viewcontent.cgi?article=1162&context=eecs_techreports).

In the repository, you can find an implementation of long numbers using the `GNU Multi-Precision library`, which will also be used in the tests.

## Building and Testing

To build the code and run tests, you can use an IDE (for example, CLion has integration with googletests).
Some useful links and tips for setting up CLion can be found on the [course page](https://cpp-kt.github.io/course/ide/clion.html).

## Bitwise Operations for Long Integers

For bitwise operations, you can think of `big_integer`'s as numbers of infinite bit length. For example, the number `11` can be represented in binary as `11 = 000..0001011`, containing an infinite number of zeros in the higher bits. Similarly, the number `-6` can be represented as `-6 = 111..1111010`, where an infinite number of ones are stored in the higher bits. Bitwise operations are defined bit by bit:
```
c == a & b <=> forall n ∈ [0..+∞) (n-th bit of c) == (n-th bit of a) & (n-th bit of b)
```
Thus `11 & -6 = 000..0001011 & 111..1111010 = 00..001010 = 10`.

Similarly, bitwise operations can be defined for bitwise `or`, `xor`, `not`, and shifts.

