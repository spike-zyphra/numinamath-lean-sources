import Mathlib

/- Which decimal digits occur as the final digit of a fourth power of an integer? -/
theorem number_theory_4663 (n : ℤ) :
    n^4 ≡ 0 [ZMOD 10] ∨
    n^4 ≡ 1 [ZMOD 10] ∨
    n^4 ≡ 5 [ZMOD 10] ∨
    n^4 ≡ 6 [ZMOD 10] := by
  have hn : n ≡ n % 10 [ZMOD 10] := Eq.symm <| Int.mod_modEq n 10
  -- To determine which decimal digits can appear as the final digit of a fourth power of an integer, we can analyze the fourth powers of the digits from 0 to 9.
  have : 0 ≤ n % 10 := Int.emod_nonneg _ (by norm_num)
  have : n % 10 < 10 := Int.emod_lt_of_pos _ (by norm_num)
  interval_cases n % 10
  all_goals replace hn := Int.ModEq.pow 4 hn
  -- 1. Calculate the fourth power of each digit:
  --  - \(0^4 = 0\) (final digit is 0)
  --  - \(1^4 = 1\) (final digit is 1)
  --  - \(2^4 = 16\) (final digit is 6)
  --  - \(3^4 = 81\) (final digit is 1)
  --  - \(4^4 = 256\) (final digit is 6)
  --  - \(5^4 = 625\) (final digit is 5)
  --  - \(6^4 = 1296\) (final digit is 6)
  --  - \(7^4 = 2401\) (final digit is 1)
  --  - \(8^4 = 4096\) (final digit is 6)
  --  - \(9^4 = 6561\) (final digit is 1)
  . left
    rwa [zero_pow (by norm_num)] at hn
  . right; left
    rwa [one_pow] at hn
  . right; right; right
    trans 16
    . rwa [show 2^4=(16 : ℤ) by norm_num] at hn
    . decide
  . right; left
    trans 81
    . rwa [show 3^4=(81 : ℤ) by norm_num] at hn
    . decide
  . right; right; right
    trans 256
    . rwa [show 4^4=(256 : ℤ) by norm_num] at hn
    . decide
  . right; right; left
    trans 625
    . rwa [show 5^4=(625 : ℤ) by norm_num] at hn
    . decide
  . right; right; right
    trans 1296
    . rwa [show 6^4=(1296 : ℤ) by norm_num] at hn
    . decide
  . right; left
    trans 2401
    . rwa [show 7^4=(2401 : ℤ) by norm_num] at hn
    . decide
  . right; right; right
    trans 4096
    . rwa [show 8^4=(4096 : ℤ) by norm_num] at hn
    . decide
  . right; left
    trans 6561
    . rwa [show 9^4=(6561 : ℤ) by norm_num] at hn
    . decide
