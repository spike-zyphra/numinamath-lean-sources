import Mathlib

/-
Show that if \( a \) is an even integer, then \( a^{2} \equiv 0 \mod 4 \), and if \( a \) is an odd integer, then \( a^{2} \equiv 1 \mod 4 \).
-/
theorem number_theory_4651 {n : ℤ} : (Even n → n^2 % 4 = 0) ∧ (Odd n → n^2 % 4 = 1) := by
  -- To prove this proposition, we need to consider two cases: when $a$ is an even integer and when $a$ is an odd integer.
  constructor <;> intro h
  · -- 1. $a$ is even:
    simp_all
    -- Given that n is even, 2 ∣ n; then we can get 2^2 ∣ n^2
    have : _ := (Int.pow_dvd_pow_iff (show 2 ≠ 0 by linarith)).mpr (Even.two_dvd h)
    -- this is exactly the goal
    assumption
  · -- 2. $a$ is odd:
    -- this goal is exactly the `Int.sq_mod_four_eq_one_of_odd`
    simp_all [Int.sq_mod_four_eq_one_of_odd]
