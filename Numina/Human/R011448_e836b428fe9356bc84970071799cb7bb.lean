import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_14025 :
  IsGreatest {x | ∃ a b : ℝ, a ∈ Icc 0 2 ∧ b ∈ Icc 0 2 ∧ x = a^2 - a + |b - a|} 4 := by
  constructor
  · use 2, 0
    norm_num
  · rintro x ⟨a, b, ha, hb, hx⟩
    rw [mem_Icc] at ha hb
    have h1 : a ^ 2 - a + |b - a| ≤ 4 := by
      by_cases h : b ≥ a
      · -- case 1 : b ≥ a
        rw [abs_of_nonneg (by linarith)]
        nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2)]
      · -- case 2 : b < a
        rw [abs_of_neg (by linarith)]
        nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2)]
    linarith [hx, h1]