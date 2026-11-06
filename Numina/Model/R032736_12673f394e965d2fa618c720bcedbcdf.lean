import Mathlib

theorem algebra_96472 (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (p1 p2 : ℝ → ℝ) (hp1 : ∀ x, p1 x = a * x ^ 2 - 2) (hp2 : ∀x, p2 x = 4 - b * x ^ 2)
(h1 : ∃ x1 x2 y1 y2 : ℝ, x1 ≠ x2 ∧ p1 x1 = 0 ∧ p1 x2 = 0 ∧ p2 x1 = 0 ∧ p2 x2 = 0 ∧ y1 ≠ y2 ∧ p1 0 = y1 ∧ p2 0 = y2 ∧ (x2 - x1) * (y2 - y1) = 2 * 12) :
a + b = 1.5 := by 
  rcases h1 with ⟨x1, x2, y1, y2, hx12, h1x1, h1x2, h2x1, h2x2, h_ne, h10, h20, h3⟩
  have eq1 : a * x1 ^ 2 - 2 = 0 := by
    rw [hp1 x1] at h1x1 
    linarith 
  have eq2 : a * x2 ^ 2 - 2 = 0 := by
    rw [hp1 x2] at h1x2 
    linarith
  have eq3 : 4 - b * x1 ^ 2 = 0 := by 
    rw [hp2 x1] at h2x1 
    linarith
  have eq4 : 4 - b * x2 ^ 2 = 0 := by 
    rw [hp2 x2] at h2x2 
    linarith
  have eq5 : p1 0 = -2 := by 
    rw [hp1 0]
    norm_num 
  have eq6 : p2 0 = 4 := by 
    rw [hp2 0]
    norm_num 
  have eq7 : y1 = -2 := by 
    linarith [eq5, h10]
  have eq8 : y2 = 4 := by 
    linarith [eq6, h20]
  rw [eq7] at h3
  rw [eq8] at h3
  have eq9 : x1 ^ 2 = x2 ^ 2 := by
    have eq10 : a * x1 ^ 2 = 2 := by linarith [eq1]
    have eq11 : a * x2 ^ 2 = 2 := by linarith [eq2]
    have eq12 : a * x1 ^ 2 = a * x2 ^ 2 := by linarith [eq10, eq11]
    have eq13 : x1 ^ 2 = x2 ^ 2 := by 
      apply (mul_left_inj' ha).mp 
      linarith 
    exact eq13
  have eq10 : x1 = -x2 := by 
    have h : x1 ^ 2 = x2 ^ 2 := eq9 
    have eq11 : x1 = x2 ∨ x1 = -x2 := by 
      apply sq_eq_sq_iff_eq_or_eq_neg.mp 
      linarith 
    cases eq11 with
    | inl heq12 =>
      exfalso 
      exact hx12 heq12
    | inr heq12 =>
      linarith 
  have eq8 : (x2 - x1) * 6 = 24 := by 
    nlinarith 
  have eq11 : x2 = 2 := by
    nlinarith [eq10, eq8]
  have eq12 : x1 = -2 := by 
    nlinarith [eq10, eq11]
  have eq13 : a = 1 / 2 := by 
    rw [eq12] at eq1 
    nlinarith 
  have eq14 : b = 1 := by 
    rw [eq12] at eq3 
    nlinarith 
  rw [eq13, eq14]
  norm_num