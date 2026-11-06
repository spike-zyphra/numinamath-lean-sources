import Mathlib

theorem algebra_19597 : IsGreatest {b : ℝ | ∃ x y, x ≠ y ∧ x^2 + b * x + 18 = 0 ∧ y^2 + b * y + 18 = 0 ∧ x / y = 2} 9 := by
  constructor
  · -- Show 9 is achievable with x = -6 and y = -3
    use -6, -3
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    all_goals norm_num
  · -- Show no value greater than 9 is in the set
    intro b hb
    rcases hb with ⟨x, y, hneq, hx, hy, hxy⟩
    have h1 : y ≠ 0 := by
      by_contra h
      have h2 : x / y = 0 := by
        rw [h]
        norm_num
      linarith [hxy, h2]
    have h2 : x = 2 * y := by
      have hne : y ≠ 0 := h1
      field_simp at hxy
      linarith
    have h3 : x ^ 2 + b * x + 18 = 0 := by linarith [hx]
    have h4 : y ^ 2 + b * y + 18 = 0 := by linarith [hy]
    have h5 : (x - y) * (x + y + b) = 0 := by
      nlinarith [h3, h4]
    cases' (mul_eq_zero.1 h5) with h6 h7
    · -- x - y = 0, but x ≠ y
      exfalso
      apply hneq
      linarith
    · -- x + y + b = 0
      have hxyeq : x + y + b = 0 := by linarith
      have h8 : 3 * y = -b := by
        have h9 : x = 2 * y := h2
        rw [h9] at hxyeq
        linarith
      have h9 : y = -b / 3 := by linarith [h8]
      rw [h9] at hy
      have h10 : b ^ 2 = 81 := by
        nlinarith
      nlinarith [sq_nonneg (b + 9), sq_nonneg (b - 9)]