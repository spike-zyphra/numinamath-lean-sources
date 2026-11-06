import Mathlib

/- What is the remainder when 100 ! is divided by 101 ? -/
theorem number_theory_610914 : Nat.factorial 100 % 101 = 100 := by
  -- Use Wilson's theorem, 100! = -1 as an element of ZMod 101.
  have h := @ZMod.wilsons_lemma 101 (by decide)
  -- Simplify the expression.
  rw [show 101 - 1 = 100 by norm_num,
      show (-1 : ZMod 101) = (100 : ℕ) by decide,
      -- Eliminate the ZMod.
      ZMod.eq_iff_modEq_nat] at h
  -- We get the desired result.
  exact h
