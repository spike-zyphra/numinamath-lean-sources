import Mathlib

theorem algebra_203959 {a b : ℝ} (h : ∃ p q r : ℝ, ∀ x : ℝ, x^4 + x^3 + 2 * x^2 + a * x + b = (p*x^2 + q * x + r)^2) :
    b = 49 / 64 := by 
  rcases h with ⟨p, q, r, h_eq⟩
  have eq1 := h_eq 1
  have eq2 := h_eq (-1)
  have eq3 := h_eq 2
  have eq4 := h_eq (-2)
  have eq5 := h_eq 3
  have eq6 := h_eq 4
  have eq7 := h_eq 5
  have eq8 := h_eq (0 : ℝ)
  ring_nf at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8
  have eq1' : b = r ^ 2 := by
    nlinarith
  -- Solving this system of equations to find b
  have eq2' : p^2=1 := by
    nlinarith [sq_nonneg (p), sq_nonneg (q), sq_nonneg (r)]
  -- Solving this system of equations to find b
  have eq3' : 2*p*q=1 := by 
    nlinarith [sq_nonneg (p), sq_nonneg (q), sq_nonneg (r)]
  -- Solving this system of equations to find b
  have eq4' : 2*p*r + q^2=2 := by
    nlinarith [sq_nonneg (p), sq_nonneg (q), sq_nonneg (r)]
  have hp : p = 1 ∨ p = -1 := by 
    have h1 : p^2 = 1 := eq2'
    have : p = 1 ∨ p = -1 := by 
      rw [sq_eq_one_iff] at h1 
      tauto 
    assumption 
  cases hp with 
  | inl hp_1 =>
    have hq1 : q = 1 / 2 := by 
      rw [hp_1] at eq3' 
      linarith 
    have hr1 : r = 7 / 8 := by 
      rw [hp_1] at eq4' 
      rw [hq1] at eq4' 
      linarith 
    rw [hr1] at eq1' 
    nlinarith 
  | inr hp_neg1 =>
    have hq2 : q = -1 / 2 := by 
      rw [hp_neg1] at eq3' 
      linarith 
    have hr2 : r = -7 / 8 := by 
      rw [hp_neg1] at eq4' 
      rw [hq2] at eq4' 
      linarith 
    rw [hr2] at eq1' 
    nlinarith