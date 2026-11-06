import Mathlib

theorem algebra_318902 {f : ℝ → ℝ} (hf : ∀ x, f x = 3 * Real.sin x + 2 * Real.cos x + 1)
    (a b c : ℝ) (h : ∀ x, a * f x + b * f (x - c) = 1) :
    b * Real.cos c / a = -1 := by

  have f_eq : ∀ x, f x = 3 * Real.sin x + 2 * Real.cos x + 1 := by 
    intro x 
    specialize hf x 
    simpa using hf
  have eq1 := h 0
  rw [f_eq 0, f_eq (0 - c)] at eq1
  have eq2 := h (Real.pi / 2)
  rw [f_eq (Real.pi / 2), f_eq (Real.pi / 2 - c)] at eq2
  have eq3 := h Real.pi
  rw [f_eq Real.pi, f_eq (Real.pi - c)] at eq3
  have eq4 := h (Real.pi / 2 + c)
  rw [f_eq (Real.pi / 2 + c), f_eq (Real.pi / 2 + c - c)] at eq4
  simp [Real.sin_sub, Real.cos_sub, Real.sin_add, Real.cos_add, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi, Real.cos_pi] at eq1 eq2 eq3 eq4 
  have h1 : a ≠ 0 := by
    nlinarith [eq1, eq2, eq3, eq4]
  have h2 : b * Real.cos c = -a := by
    nlinarith [eq1, eq2, eq3, eq4]
  have h3 : b * Real.cos c / a = -1 := by 
    field_simp [h1]
    linarith [h2]
  exact h3