import Mathlib

theorem algebra_196004 {a b : ℝ} (ha : a ≠ -1) (hb : b ≠ 1)
    (h : a - b + 2 ≠ 0) (h1 : a + 1 / (a + 1) = b + 1 / (b - 1) - 2)
    (P : ℝ) (hP : P = a * b - a + b) : P = 2 := by
  have h2 : a + 1 ≠ 0 := by
    intro h'
    apply ha
    linarith
  have h3 : b - 1 ≠ 0 := by
    intro h'
    apply hb
    linarith
  have h4 : (a + 1 / (a + 1)) * ((a + 1) * (b - 1)) = (b + 1 / (b - 1) - 2) * ((a + 1) * (b - 1)) := by
    rw [h1]
  have h5 : (a + 1 / (a + 1)) * ((a + 1) * (b - 1)) = a * (a + 1) * (b - 1) + (b - 1) := by
    field_simp [(show a + 1 ≠ 0 by assumption), (show b - 1 ≠ 0 by assumption)]
    all_goals ring
  have h6 : (b + 1 / (b - 1) - 2) * ((a + 1) * (b - 1)) = b * (a + 1) * (b - 1) + (a + 1) - 2 * (a + 1) * (b - 1) := by
    field_simp [(show a + 1 ≠ 0 by assumption), (show b - 1 ≠ 0 by assumption)]
    all_goals ring
  rw [h5, h6] at h4
  have eq1 : (a - b + 2) * ((a + 1) * (b - 1) - 1) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp eq1) with h7 h8
  · -- If a - b + 2 = 0, which contradicts h.
    exfalso
    apply h
    linarith
  · -- If (a + 1) * (b - 1) - 1 = 0, then P = 2.
    have h9 : (a + 1) * (b - 1) = 1 := by
      linarith
    have h10 : a * b - a + b = 2 := by
      nlinarith
    rw [hP]
    linarith [h10]