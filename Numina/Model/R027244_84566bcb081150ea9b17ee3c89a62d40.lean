import Mathlib

theorem algebra_135011 (x : ℝ) (hx : x ≠ -1) (hx' : x ≠ -2) (hx'' : x ≠ -3)
    (h : 1 + 3 / (x + 3) * (1 + 2 / (x + 2) * (1 + 1 / (x + 1))) = x) :
    x = 2 := by
  have eq1 : 1 + 3 / (x + 3) * (1 + 2 / (x + 2) * (1 + 1 / (x + 1))) = (x + 4) / (x + 1) := by
    have hx1 : x + 1 ≠ 0 := by
      intro h1
      apply hx
      linarith
    have hx2 : x + 2 ≠ 0 := by
      intro h2
      apply hx'
      linarith
    have hx3 : x + 3 ≠ 0 := by
      intro h3
      apply hx''
      linarith
    field_simp [(show x + 1 ≠ 0 by assumption), (show x + 2 ≠ 0 by assumption), (show x + 3 ≠ 0 by assumption)]
    ring
  rw [eq1] at h
  have hx1 : x + 1 ≠ 0 := by
    intro h1
    apply hx
    linarith
  have h1 : x + 4 = x * (x + 1) := by
    field_simp [hx1] at h
    nlinarith
  have h2 : x^2 = 4 := by
    nlinarith
  have h3 : x = 2 ∨ x = -2 := by
    have h4 : x^2 - 4 = 0 := by
      linarith
    have h5 : (x - 2) * (x + 2) = 0 := by
      nlinarith
    cases (mul_eq_zero.mp h5) with
    | inl h6 => 
      left
      linarith
    | inr h7 => 
      right
      linarith
  cases h3 with
  | inl h4 => 
    exact h4
  | inr h4 => 
    exfalso
    apply hx'
    linarith