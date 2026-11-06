import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_263804 {f : ℝ → ℝ} (hf : f = λ x => x^2 + 2 * (a - 1) * x + 2)
  (ha : ∀ x ∈ Ioi (-4), deriv f x > 0) :
  a ≥ 5 := by
  have hf' : deriv f = λ x => 2 * x + 2 * (a - 1) := by 
    funext x
    rw [hf]
    simp [deriv_pow, deriv_const_mul, deriv_add, deriv_const, mul_comm]
    all_goals field_simp
    <;> ring
  have h1 : ∀ x ∈ Ioi (-4), 2 * x + 2 * (a - 1) > 0 := by
    intro x hx
    specialize ha x hx
    rw [hf'] at ha 
    simpa using ha
  by_contra h
  push_neg at h 
  have h2 := h1 (-4 + (5 - a) / 2) (by
    have h2 : (-4 + (5 - a) / 2 : ℝ) > -4 := by
      nlinarith 
    exact h2
  )
  have h3 : 2 * (-4 + (5 - a) / 2) + 2 * (a - 1) > 0 := by 
    simpa using h2
  nlinarith