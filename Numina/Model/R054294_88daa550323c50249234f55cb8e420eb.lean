import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_62971 {x : ℝ} (hx : x > 0) (h : 40 / (x - 10) = 10 / x) :
    x = 10 * sqrt 5 := by
  have h1 : x ≠ 0 := by linarith
  have h2 : x - 10 ≠ 0 := by
    by_contra h3
    have : x = 10 := by linarith
    rw [this] at h
    field_simp [h1] at h <;> linarith
  have eq1 : 40 * x = 10 * (x - 10) := by
    field_simp [(show x - 10 ≠ 0 by assumption), (show x ≠ 0 by linarith)] at h ⊢
    nlinarith

  nlinarith [show sqrt 5 > 0 by positivity]