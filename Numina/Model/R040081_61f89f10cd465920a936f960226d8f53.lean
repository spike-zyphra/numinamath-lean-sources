import Mathlib

theorem algebra_17049 : IsGreatest {x : ℝ | √(2 * x) = 4 * x} (1 / 8) := by
  constructor
  · -- Show that 1/8 is in the set
    show √(2 * (1 / 8 : ℝ)) = 4 * (1 / 8 : ℝ)
    have h1 : (2 * (1 / 8 : ℝ)) = (1 / 4 : ℝ) := by norm_num
    rw [h1]
    have h2 : √(1 / 4 : ℝ) = 1 / 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h2]
    norm_num
  · -- Show that for any x in the set, x ≤ 1/8
    intro x hx
    have h_eq : √(2 * x) = 4 * x := hx
    have h1 : 2 * x ≥ 0 := by
      by_contra h
      push_neg at h
      have h2 : x < 0 := by nlinarith
      have h3 : 2 * x < 0 := by linarith
      have h4 : √(2 * x) = 0 := by
        rw [Real.sqrt_eq_zero']
        linarith
      have h5 : 4 * x = 0 := by
        nlinarith [h_eq, h4]
      have h6 : x = 0 := by
        linarith
      linarith
    have h2 : (√(2 * x)) ^ 2 = (4 * x) ^ 2 := by
      rw [h_eq]
    have h3 : (√(2 * x)) ^ 2 = 2 * x := by
      have h4 : 2 * x ≥ 0 := h1
      have h5 : (√(2 * x)) ^ 2 = 2 * x := Real.sq_sqrt (by linarith)
      linarith
    have h4 : (4 * x) ^ 2 = 16 * x ^ 2 := by ring
    have h5 : 2 * x = 16 * x ^ 2 := by
      nlinarith [h2, h3, h4]
    have h6 : x * (8 * x - 1) = 0 := by
      nlinarith [h5]
    cases' (mul_eq_zero.mp h6) with h7 h8
    · -- Case where x = 0
      have hx0 : x = 0 := by
        linarith
      linarith
    · -- Case where 8 * x - 1 = 0
      have hx1 : x = 1 / 8 := by
        linarith
      linarith [hx1]