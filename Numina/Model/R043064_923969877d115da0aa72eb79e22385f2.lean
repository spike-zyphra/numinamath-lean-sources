import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_21715 {f : ℝ → ℝ}
  (hf : f = λ x => 1 / (abs (x ^ 2 - 6 * x + 8) + abs (x ^ 2 + x - 6))) :
  ∀ x, x ≠ 2 → f x ∈ Ioi 0 := by
  intro x hx
  rw [hf]
  have h1 : abs (x ^ 2 - 6 * x + 8) + abs (x ^ 2 + x - 6) > 0 := by
    by_contra h
    push_neg at h
    have h2 : abs (x ^ 2 - 6 * x + 8) ≥ 0 := by apply abs_nonneg
    have h3 : abs (x ^ 2 + x - 6) ≥ 0 := by apply abs_nonneg
    have h4 : abs (x ^ 2 - 6 * x + 8) = 0 := by linarith
    have h5 : abs (x ^ 2 + x - 6) = 0 := by linarith
    have h6 : x ^ 2 - 6 * x + 8 = 0 := by
      rw [abs_eq_zero] at h4
      linarith
    have h7 : x ^ 2 + x - 6 = 0 := by
      rw [abs_eq_zero] at h5
      linarith
    have h8 : (x - 2) * (x - 4) = 0 := by 
      nlinarith 
    have h9 : (x + 3) * (x - 2) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.mp h8) with h10 h11
    · -- Case x - 2 = 0, so x = 2
      have h12 : x = 2 := by linarith
      tauto
    · -- Case x - 4 = 0, so x = 4
      have h13 : x = 4 := by linarith
      rw [show x = 4 by linarith] at h9
      nlinarith
  have h2 : 1 / (abs (x ^ 2 - 6 * x + 8) + abs (x ^ 2 + x - 6)) > 0 := by
    apply div_pos
    norm_num
    all_goals linarith
  exact h2