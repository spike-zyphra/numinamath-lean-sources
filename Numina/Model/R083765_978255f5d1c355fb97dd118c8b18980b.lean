import Mathlib

theorem algebra_199828 (a : ℝ) (h : ∃ x1 x2, x1 ≠ x2 ∧ 3*x1^2+a*x1-2=0 ∧ 3*x2^2+a*x2-2=0 ∧ 6*x1+x2=0) :
    a=5 ∨ a=-5 := by
  rcases h with ⟨x1, x2, hx12, h1, h2, h3⟩
  have h4 : x1 - x2 ≠ 0 := by
    intro h'
    apply hx12
    linarith
  have h5 : 3 * (x1 + x2) + a = 0 := by
    have h6 : 3 * (x1 ^ 2 - x2 ^ 2) + a * (x1 - x2) = 0 := by
      nlinarith
    have eq1 : 3 * (x1 ^ 2 - x2 ^ 2) + a * (x1 - x2) = (x1 - x2) * (3 * (x1 + x2) + a) := by
      ring
    rw [eq1] at h6
    cases' (mul_eq_zero.mp h6) with h7 h8
    · -- Case where $x1 - x2 = 0$
      exfalso
      exact hx12 (by linarith)
    · -- Case where $3*(x1 + x2) + a = 0$
      linarith
  have hx2 : x2 = -6 * x1 := by linarith
  have ha1 : a = 15 * x1 := by
    rw [hx2] at h5
    linarith
  rw [hx2, ha1] at h2
  have eq1 : 18 * x1 ^ 2 - 2 = 0 := by
    nlinarith
  have h9 : x1 ^ 2 = 1 / 9 := by
    linarith
  have h10 : x1 = 1 / 3 ∨ x1 = -1 / 3 := by
    have h11 : x1 ^ 2 - (1 / 9) = 0 := by linarith
    have h12 : (x1 - 1 / 3) * (x1 + 1 / 3) = 0 := by
      linarith
    cases' (mul_eq_zero.mp h12) with h14 h15
    · -- First case where $x1 - 1/3 = 0$
      left
      linarith
    · -- Second case where $x1 + 1/3 = 0$
      right
      linarith
  cases h10 with
  | inl h11 =>
    left
    rw [h11] at ha1
    linarith
  | inr h13 =>
    right
    rw [h13] at ha1
    linarith