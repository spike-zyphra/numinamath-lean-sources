import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_327341 {a : ℝ} (ha : ∀ x : ℝ, x < 1 ∨ x > 5 → x^2 - 2*(a-2)*x + a > 0) :
    a ∈ Ioc 1 5 := by
  have h1 : a > 1 := by
    by_contra h
    push_neg at h
    have h1 := ha (-1) (Or.inl (by norm_num))
    nlinarith
  have h5 : a ≤ 5 := by
    by_contra h
    push_neg at h
    have h2 := ha (5 + (a - 5) / 2) (Or.inr (by
      nlinarith
    ))
    nlinarith [sq_nonneg (a - 5), sq_nonneg (a - 1), sq_nonneg (a - 4)]
  constructor
  · -- Show that 1 < a
    linarith
  · -- Show that a ≤ 5
    linarith