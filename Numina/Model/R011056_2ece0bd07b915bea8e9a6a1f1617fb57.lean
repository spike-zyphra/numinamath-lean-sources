import Mathlib

theorem algebra_9189 (x : ℝ) (hx1 : x ^ 2 + x ≠ 0) (hx2 : x ^ 2 - x ≠ 0) :
    4 / (x ^ 2 + x) - 3 / (x ^ 2 - x) = 0 ↔ x = 7 := by
  constructor
  · -- Forward direction: Equation to x = 7
    intro h
    have h1 : x ≠ 0 := by
      by_contra h'
      have : x ^ 2 + x = 0 := by
        rw [h']
        norm_num
      contradiction
    have h2 : x + 1 ≠ 0 := by
      by_contra h'
      have h1 : x = -1 := by linarith
      have : x ^ 2 + x = 0 := by
        rw [h1]
        norm_num
      contradiction
    have h3 : x - 1 ≠ 0 := by
      by_contra h'
      have h1 : x = 1 := by linarith
      have : x ^ 2 - x = 0 := by
        rw [h1]
        norm_num
      contradiction
    have eq1 : 4 / (x ^ 2 + x) - 3 / (x ^ 2 - x) = 0 := h
    have eq2 : 4 / (x ^ 2 + x) - 3 / (x ^ 2 - x) =
        (4 * (x ^ 2 - x) - 3 * (x ^ 2 + x)) / ((x ^ 2 + x) * (x ^ 2 - x)) := by
      field_simp [show x ^ 2 + x ≠ 0 by assumption, show x ^ 2 - x ≠ 0 by assumption]
      <;> ring
    rw [eq2] at eq1
    have eq3 : 4 * (x ^ 2 - x) - 3 * (x ^ 2 + x) = 0 := by
      have hxne0 : (x ^ 2 + x) * (x ^ 2 - x) ≠ 0 := by
        apply mul_ne_zero
        all_goals
          assumption
      field_simp [hxne0] at eq1
      <;> nlinarith
    have eq4 : x * (x - 7) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 eq4) with h5 h6
    · -- Case h5, x = 0
      exfalso
      have h4 : x = (0 : ℝ) := by linarith
      contradiction
    · -- Case h6, x - 7 = 0
      linarith
  · -- Backward direction: x = 7 implies equation
    intro h
    rw [h]
    norm_num