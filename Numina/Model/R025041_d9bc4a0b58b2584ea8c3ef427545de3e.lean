import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_11221 (f : ℝ → ℝ) (a : ℝ)
  (hf : ∀ x, f x = (x^2 + (a-1)*x + 1) * exp x)
  (h : ∀ x, f x + exp 2 ≥ 0) :
  a ∈ Icc (-2) (exp 3 + 3) := by
  have h2 : a ≥ -2 := by
    have h1 := h 2
    simp [hf] at h1
    norm_num at h1
    nlinarith [Real.exp_pos 2]
  have h3 : a ≤ exp 3 + 3 := by
    have h4 := h (-1)
    have eq4 : f (-1) = ((-1 : ℝ) ^ 2 + (a - 1) * (-1) + 1) * exp (-1 : ℝ) := hf (-1)
    rw [eq4] at h4
    have eq1 : ((-1 : ℝ) ^ 2 + (a - 1) * (-1 : ℝ) + 1) * exp (-1 : ℝ) + exp 2 ≥ 0 := by linarith
    have eq2 : ((-1 : ℝ) ^ 2 + (a - 1) * (-1 : ℝ) + 1) * exp (-1 : ℝ) + exp 2 = (3 - a) * exp (-1) + exp 2 := by
      ring_nf
    rw [eq2] at eq1
    have eq3 : (3 - a) * exp (-1) + exp 2 = (3 - a + exp 3) * exp (-1) := by
      have h6 : exp 2 = exp (-1 : ℝ) * exp (3 : ℝ) := by
        calc
          exp (2 : ℝ) = exp ((-1 : ℝ) + (3 : ℝ)) := by ring_nf
          _ = exp (-1 : ℝ) * exp (3 : ℝ) := by rw [Real.exp_add]
      rw [h6]
      ring
    rw [eq3] at eq1
    have h7 : exp (-1 : ℝ) > 0 := Real.exp_pos (-1)
    have h8 : (3 - a + exp 3) ≥ 0 := by
      by_contra h9
      push_neg at h9
      have h9 : (3 - a + exp 3) * exp (-1) < 0 := by
        have h10 : exp (-1 : ℝ) > 0 := Real.exp_pos (-1)
        nlinarith
      linarith
    nlinarith
  constructor
  · linarith
  · linarith