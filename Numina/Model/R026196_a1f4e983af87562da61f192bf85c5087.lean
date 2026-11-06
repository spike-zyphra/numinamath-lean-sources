import Mathlib

theorem algebra_207803 {a b : ℝ} (h : ∃ p q r : ℝ, ∀ x : ℝ, x^4 + x^3 + 2 * x^2 + a * x + b = (p*x^2 + q * x + r)^2) :
    b = 49 / 64 := by
  rcases h with ⟨p, q, r, h_eq⟩
  have eq1 := h_eq 0
  have eq2 := h_eq 1
  have eq3 := h_eq 2
  have eq4 := h_eq 3
  have eq5 := h_eq 4
  have eq6 := h_eq 5
  ring_nf at eq1 eq2 eq3 eq4 eq5 eq6
  have eq7 : p^2 = 1 := by
    nlinarith
  have eq8 : 2 * p * q = 1 := by
    nlinarith
  have eq9 : 2 * p * r + q^2 = 2 := by
    nlinarith
  have eq11 : r^2 = b := by 
    nlinarith
  have h1 : p = 1 ∨ p = -1 := by
    have hp : p^2 = 1 := eq7
    have : p = 1 ∨ p = -1 := by
      rw [sq_eq_one_iff] at hp 
      exact hp
    assumption
  rcases h1 with (hp | hp)
  · -- p = 1
    have hq : q = 1 / 2 := by 
      rw [hp] at eq8
      linarith
    have hr : r = 7 / 8 := by
      rw [hp, hq] at eq9
      nlinarith
    nlinarith [ eq11, hr ]
  · -- p = -1
    have hq : q = -1 / 2 := by
      rw [hp] at eq8
      linarith
    have hr : r = -7 / 8 := by
      rw [hp, hq] at eq9
      nlinarith
    nlinarith [ eq11, hr ]