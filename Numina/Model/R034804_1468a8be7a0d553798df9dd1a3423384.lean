import Mathlib

theorem algebra_21835 (x : ℝ) (hx : x ≠ -2) (hx' : x ≠ 2) :
    (6 - x) / (x ^ 2 - 4) = 2 + x / (x + 2) ↔ x = 7 / 3 := by
  constructor
  · -- Assume (6 - x) / (x ^ 2 - 4) = 2 + x / (x + 2), prove x = 7 / 3
    intro h
    have h1 : x ^ 2 - 4 ≠ 0 := by
      intro h1
      have : (x - 2) * (x + 2) = 0 := by nlinarith
      cases' (mul_eq_zero.1 this) with h2 h3
      · -- x - 2 = 0, so x = 2
        exfalso
        apply hx'
        linarith
      · -- x + 2 = 0, so x = -2
        exfalso
        apply hx
        linarith
    have h2 : x + 2 ≠ 0 := by
      intro h2
      apply hx
      linarith
    have eq1 : (6 - x) / (x ^ 2 - 4) = 2 + x / (x + 2) := h
    have eq2 : (6 - x) = (2 + x / (x + 2)) * (x ^ 2 - 4) := by
      have h1' : x ^ 2 - 4 ≠ 0 := h1
      field_simp [(show x + 2 ≠ 0 by exact h2), (show x - 2 ≠ 0 by
          intro hneq
          apply hx'
          linarith
      ), h1'] at eq1 ⊢
      nlinarith [sq_pos_of_ne_zero (show (x + 2) ≠ 0 by exact h2), sq_pos_of_ne_zero (show (x - 2) ≠ 0 by
          intro hneq
          apply hx'
          linarith
      )]
    have eq3 : (2 + x / (x + 2)) * (x ^ 2 - 4) = 2 * (x ^ 2 - 4) + x * (x - 2) := by
      have h2' : x + 2 ≠ 0 := h2
      field_simp [h2']
      <;> nlinarith
    rw [eq3] at eq2
    have h3 : 3 * x ^ 2 - x - 14 = 0 := by
      nlinarith [eq2]
    have h4 : (x - 7 / 3) * (x + 2) = 0 := by
      nlinarith [h3]
    cases' (mul_eq_zero.1 h4) with h5 h6
    · -- x - 7/3 = 0
      linarith
    · -- x + 2 = 0
      exfalso
      apply hx
      linarith
  · -- Assume x = 7/3 prove the equation
    intro h
    rw [h]
    norm_num