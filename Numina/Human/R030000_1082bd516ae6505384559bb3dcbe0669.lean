import Mathlib

open Nat Finset

-- Define the polynomial P(n) = (n - 2)(n)(n - 1)(n - 7)
def P (n : ℤ) : ℤ := (n - 2) * n * (n - 1) * (n - 7)

-- Example: factorization of 1001
#eval primeFactorsList 1001  -- Output: [7, 11, 13]

/-
Informal Explanation:

Let’s count how many integers `1 ≤ n ≤ 2017` satisfy `1001 ∣ P(n)`.

Note: 1001 = 7 * 11 * 13, so we require `P(n)` to be divisible by 7, 11, and 13.

### Step 1: Multiples of 7
The polynomial P(n) has factors (n - 2), n, (n - 1), and (n - 7).
That means it's divisible by 7 if n ≡ 0, 1, 2, or 7 mod 7.
But note: among these, only 3 are distinct mod 7 (0, 1, 2, and 7 ≡ 0),
so only 3 values of n mod 7 make P(n) divisible by 7.

### Step 2: Multiples of 11
We want P(n) divisible by 11.
This is trickier, but by counting, the set of n mod 11 such that P(n) ≡ 0 mod 11 has size 4.

### Step 3: Multiples of 13
Similarly, P(n) ≡ 0 mod 13 has 4 solutions mod 13.

### Step 4: CRT combinations
We now look at combinations of mod 7 × mod 11 × mod 13:
There are 3 × 4 × 4 = 48 such combinations.
By the Chinese Remainder Theorem, each triple corresponds to exactly one `n mod 1001`.

So in the interval `[1, 2017]`, there are:
- One solution in `[1, 1001]`,
- One in `[1002, 2002]`,
- And possibly one more in `[2003, 2017]`.

That gives **48 + 48 = 96** solutions in `[16, 2017]`.

### Step 5: Check small values 1 to 15
Check each `n ∈ {1, ..., 15}` manually:
- For n = 1, 2, or 7 ⇒ P(n) = 0 ⇒ divisible by 1001.
- For the rest, P(n) not divisible by 11 or 13, so no other n < 16 qualify.

Final count = 96 (main range) + 3 (small ones) = **99**.
-/

/-- Final result: number of n from 1 to 2017 such that 1001 divides P(n) -/
theorem numbertheory_609719 :
    ∑ n in Icc 1 2017, (if (1001 ∣ P n) then (1 : ℕ) else 0) = 99 := by
  native_decide
