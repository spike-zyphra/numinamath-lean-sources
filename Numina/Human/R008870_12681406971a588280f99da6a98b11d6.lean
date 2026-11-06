import Mathlib
/-Factorize $a^{2}-6$ in the real number range.-/
theorem algebra_9122 {a : ℝ} : a^2 - 6 = (a + Real.sqrt 6) * (a - Real.sqrt 6) := by
  calc
   _ = a ^ 2 - (Real.sqrt 6) ^ 2 := by simp only [Nat.ofNat_nonneg, Real.sq_sqrt]
   _ = _ := by ring