import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_102595 {f g : ℝ → ℝ}
  (hf : ∀ x > 0, f (x / 3) + 2 ≤ logb 3 x ∧ logb 3 x ≤ g x - 1)
  (hg : ∀ x > 0, g (x / 3) ≤ logb 3 x ∧ logb 3 x ≤ f x + 1) :
  ∀ x > 0, f x = logb 3 x - 1 ∧ g x = logb 3 x + 1 := by
  intro x hx
  have h1 := hf x hx
  have h2 := hg x hx
  have h3 := hf (3 * x) (by linarith)
  have h4 := hg (3 * x) (by linarith)
  have h5 : logb 3 (3 * x) = logb 3 3 + logb 3 x := by
    rw [logb_mul (by linarith) (by linarith)]
  have h6 : logb 3 (3 : ℝ) = 1 := by
    norm_num [logb_eq_iff_rpow_eq]
  have h7 : logb 3 (3 * x) = 1 + logb 3 x := by
    rw [h5, h6]
    all_goals linarith
  have hx1 : f x + 2 ≤ 1 + logb 3 x := by
    have h8 : f ((3 * x) / 3) + 2 ≤ logb 3 (3 * x) := by
      exact (h3.1)
    have h9 : (3 * x) / 3 = x := by
      ring_nf
    rw [h9] at h8
    rw [h7] at h8
    linarith
  have hx2 : g x ≤ 1 + logb 3 x := by
    have h10 : g ((3 * x) / 3) ≤ logb 3 (3 * x) := by
      exact (h4.1)
    have h9 : (3 * x) / 3 = x := by
      ring_nf
    rw [h9] at h10
    rw [h7] at h10
    linarith
  have hx3 : logb 3 x ≤ f x + 1 := by
    exact h2.2
  have hx4 : logb 3 x ≤ g x - 1 := by
    exact h1.2
  constructor
  · -- Solving for f(x)
    linarith
  · -- Solving for g(x)
    linarith