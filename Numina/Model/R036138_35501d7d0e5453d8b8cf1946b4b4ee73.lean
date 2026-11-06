import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem inequalities_191648 {f : ℝ → ℝ}
  (h : ∀ x y : ℝ, x ≠ y → ∀ q₁ q₂ : ℝ, q₁ > 0 → q₂ > 0 → q₁ + q₂ = 1 →
    f (q₁ * x + q₂ * y) > q₁ * f x + q₂ * f y) :
  (∀ u v : ℝ, u ≠ v → f u + f v < 2 * f ((u + v) / 2)) ∧
  (∀ a b : ℝ, b ≠ 0 → f a + f (a + 2 * b) < 2 * f (a + b) ∧
    f a + f (a + 3 * b) < f (a + b) + f (a + 2 * b)) := by
  constructor
  · -- Prove the first part: for all real u, v with u ≠ v, f(u) + f(v) < 2*f((u + v)/2)
    intro u v hne
    have eq1 : f ((u + v) / 2) > (f u + f v) / 2 := by
      specialize h u v (show u ≠ v by exact hne) (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
      ring_nf at h ⊢
      linarith
    linarith [eq1]
  · -- Prove the second part: for all real a, b with b ≠ 0, both inequalities hold
    intro a b hb
    have hne1 : a ≠ a + 2 * b := by
      by_contra h'
      have : 2 * b = 0 := by linarith
      have : b = 0 := by linarith
      contradiction
    have h11 : f (a + b) > (f a + f (a + 2 * b)) / 2 := by
      specialize h a (a + 2 * b) (by
          by_contra h'
          have : 2 * b = 0 := by linarith
          have : b = 0 := by linarith
          contradiction
      ) (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
      ring_nf at h ⊢
      linarith
    have h21 : f a + f (a + 2 * b) < 2 * f (a + b) := by
      linarith [h11]
    have h51 : f (a + 2 * b) > (f a) / 3 + 2 * (f (a + 3 * b)) / 3 := by
      specialize h a (a + 3 * b) (by
        by_contra h'
        have : 3 * b = 0 := by linarith
        have : b = 0 := by linarith
        contradiction
      ) (1 / 3) (2 / 3) (by norm_num) (by norm_num) (by norm_num)
      ring_nf at h ⊢
      linarith
    have h71 : f (a + b) > (2 / 3) * f a + (1 / 3) * f (a + 3 * b) := by
      specialize h a (a + 3 * b) (by
        by_contra h'
        have : 3 * b = 0 := by linarith
        have : b = 0 := by linarith
        contradiction
      ) (2 / 3) (1 / 3) (by norm_num) (by norm_num) (by norm_num)
      ring_nf at h ⊢
      linarith
    have h91 : f (a + 2 * b) + f (a + b) > f (a + 3 * b) + f a := by
      linarith [h51, h71]
    constructor
    · exact h21
    · -- Prove the second part
      linarith [h91]