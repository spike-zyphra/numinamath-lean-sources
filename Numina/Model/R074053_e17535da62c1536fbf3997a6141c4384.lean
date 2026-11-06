import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_316516 {a : ℝ} (f : ℝ → ℝ) (hf : f = λ x => (a - x) * abs x)
  (hinv : Function.LeftInverse f (λ x => -x + a)) (m : ℝ) :
  (∀ x ∈ Icc (-2) 2, f ⁻¹' {y | y = x ^ 2 + m} ⊆ Ioi 0) ↔ m > 12 := by
  have h2 := hinv 1
  have h3 := hinv 2
  simp [hf] at h2 h3
  cases' (eq_or_eq_neg_of_abs_eq h2) with h21 h22
  · -- Case $a - 1 = 1 \implies a = 2$
    have ha : a = 2 := by linarith
    rw [ha] at h3
    norm_num at h3
    all_goals linarith
  · -- Case $a - 1 = -1 \implies a = 0$
    have ha : a = 0 := by linarith
    rw [ha] at h3
    norm_num at h3
    all_goals linarith