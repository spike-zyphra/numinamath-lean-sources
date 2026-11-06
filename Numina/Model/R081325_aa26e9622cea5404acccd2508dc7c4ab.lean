import Mathlib

theorem algebra_197149 (a b c d : ℝ) :
    (∀ x : ℝ, 5*x^3-32*x^2+75*x-71=a*(x-2)^3+b*(x-2)^2+c*(x-2)+d) ↔
    a = 5 ∧ b = -2 ∧ c = 7 ∧ d = -9 := by 
  constructor
  · -- Forward direction: from identity to coefficients
    intro h
    have eq1 := h 2
    have eq2 := h 3
    have eq3 := h 1
    have eq4 := h 4
    have eq5 := h 0
    have h1 : d = -9 := by 
      nlinarith
    have h2 : a = 5 := by 
      simp [h1] at eq2 eq3 eq4 eq5
      nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d)]
    have h3 : b = -2 := by
      simp [h1, h2] at eq2 eq3 eq4 eq5
      nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d)]
    have h4 : c = 7 := by
      simp [h1, h2, h3] at eq2 eq3 eq4 eq5
      nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d)]
    exact ⟨h2, h3, h4, h1⟩
  · -- Reverse direction: from coefficients to identity
    rintro ⟨ha, hb, hc, hd⟩
    intro x
    rw [ha, hb, hc, hd]
    ring