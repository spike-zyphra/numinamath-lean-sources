import Mathlib

/-Two positive integers each have a units digit of 2 when expressed in base 4.  Find the units digit of their product when expressed in base 4.-/
theorem number_theory_19618 (a b : ℕ) (ha : a % 4 = 2) (hb : b % 4 = 2) :
    (a * b) % 4 = 0 := by
  -- easily show that a * b ≡ 0 [MOD 4]
  rw [Nat.mul_mod]
  rw [ha, hb]