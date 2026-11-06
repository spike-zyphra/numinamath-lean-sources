import Mathlib

open Polynomial

theorem algebra_7870 (a : ℝ) (g : ℝ → ℝ) (hg : g = fun x => x^3 + a * x + 2500)
    (hroot : ∃ x1 x2, x1 ≠ x2 ∧ g x1 = 0 ∧ g x2 = 0 ∧ x1 = 4 * x2) :
    a = -525 := by 
  obtain ⟨x1, x2, hx12, hx1, hx2, hx14x2⟩ := hroot
  have eq1 : x1^3 + a * x1 + 2500 = 0 := by 
    rw [hg] at hx1
    exact hx1
  have eq2 : x2^3 + a * x2 + 2500 = 0 := by 
    rw [hg] at hx2
    exact hx2
  rw [show x1 = 4 * x2 by linarith [hx14x2]] at eq1
  have eq3 : 64 * x2^3 + 4 * a * x2 + 2500 - (x2^3 + a * x2 + 2500) = 0 := by
    nlinarith
  have eq4 : 63 * x2^3 + 3 * a * x2 = 0 := by
    nlinarith 
  have eq5 : 3 * x2 * (21 * x2^2 + a) = 0 := by
    nlinarith
  cases (mul_eq_zero.mp eq5) with 
  | inl h =>
    have hx20 : x2 = 0 := by 
      linarith
    rw [hx20] at eq2
    nlinarith
  | inr h =>
    have ha : a = -21 * x2^2 := by 
      nlinarith 
    rw [ha] at eq2
    have eq6 : x2^3 + (-21 * x2^2) * x2 + 2500 = 0 := by 
      nlinarith 
    have hx25 : x2^3 = 125 := by 
      nlinarith [eq6]
    have hx25' : x2 = 5 := by 
      have h1 : x2^3 - 125 = 0 := by 
        nlinarith [hx25]
      have h2 : (x2 - 5) * (x2^2 + 5 * x2 + 25) = 0 := by 
        ring_nf at h1 ⊢
        nlinarith 
      cases (mul_eq_zero.mp h2) with 
      | inl h => 
        linarith 
      | inr h => 
        have h3 : x2^2 + 5 * x2 + 25 > 0 := by 
          nlinarith [sq_nonneg (x2 + 5 / 2)]
        nlinarith 
    have ha' : a = -525 := by 
      rw [hx25'] at ha 
      nlinarith 
    linarith [ha']