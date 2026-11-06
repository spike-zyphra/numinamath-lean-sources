import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_104766 (f : ℝ → ℝ) (hf : f = λ x => 1 + cos x) :
    ∫ x in (-π)..π, max (f x) 0 = 2 * π := by 
  have h1 : ∀ x : ℝ, max (f x) 0 = 1 + cos x := by
    intro x
    rw [hf]
    have h2 : cos x ≥ -1 := by
      linarith [neg_one_le_cos x, cos_le_one x]
    have h3 : 1 + cos x ≥ 0 := by linarith
    simp [max_eq_left_of_lt, h3]
    all_goals linarith
  simp_rw [h1]
  <;> norm_num [Real.sin_pi, Real.cos_pi]
  <;> ring_nf <;> norm_num [Real.sin_pi, Real.cos_pi]