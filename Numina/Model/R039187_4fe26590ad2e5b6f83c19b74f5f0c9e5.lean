import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_225078 (a : ℝ) (f : ℝ → ℝ) (hf : f = λ x => x^2 - 2 * a * x + a^2)
  (h : ∀ x < 1, deriv f x < 0) :
  a ≥ 1 := by 
  have h1 : deriv f = λ x => 2 * x - 2 * a := by 
    rw [hf]
    funext x
    simp [deriv_pow, deriv_sub, deriv_add, deriv_const, mul_comm]
    <;> field_simp <;> ring
  have h2 : ∀ x < 1, (2 * x - 2 * a) < 0 := by 
    intro x hx
    have hfx : deriv f x < 0 := h x hx
    rw [h1] at hfx
    exact hfx
  by_contra h3
  push_neg at h3
  have h4 : a < 1 := h3
  have h5 : a < (a + 1) / 2 := by
    linarith 
  have h6 : (a + 1) / 2 < 1 := by
    linarith 
  have h7 := h2 ((a + 1) / 2) (by linarith)
  have h8 : 2 * ((a + 1) / 2 : ℝ) - 2 * a ≥ 0 := by 
    nlinarith 
  linarith