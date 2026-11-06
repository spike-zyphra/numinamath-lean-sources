import Mathlib

theorem algebra_98478 (x y : ℝ) (h : 5 * x + 12 * y = 60) :
    IsLeast {z | ∃ x y : ℝ, 5 * x + 12 * y = 60 ∧ z = Real.sqrt (x ^ 2 + y ^ 2)} (60 / 13) := by
  constructor
  · -- Show 60/13 is achievable
    use 300 / 169, 720 / 169
    constructor
    · -- Show that these satisfy the linear equation
      norm_num
    · -- Show that the distance is 60/13
      have h1 : Real.sqrt ((300 / 169: ℝ) ^ 2 + (720 / 169: ℝ) ^ 2) = 60 / 13 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      linarith [h1]
  · -- Show 60/13 is the least element
    intro z hz
    rcases hz with ⟨x, y, hx, hz⟩
    have h2 : x ^ 2 + y ^ 2 >= (60 / 13) ^ 2 := by
      have h3 : 5 * x + 12 * y = 60 := by
        linarith
      nlinarith [sq_nonneg (12 * x - 5 * y), sq_nonneg (x - 300 / 169), sq_nonneg (y - 720 / 169),
        sq_nonneg (5 * x + 12 * y - 60)]
    have h3 : Real.sqrt (x ^ 2 + y ^ 2) >= 60 / 13 := by
      have h4 : x ^ 2 + y ^ 2 >= (60 / 13) ^ 2 := h2
      have h5 : Real.sqrt (x ^ 2 + y ^ 2) >= Real.sqrt ((60 / 13) ^ 2) := Real.sqrt_le_sqrt (by linarith)
      have h6 : Real.sqrt ((60 / 13 : ℝ) ^ 2) = (60 / 13 : ℝ) := Real.sqrt_sq (by norm_num)
      linarith [h5, h6, h4]
    linarith [hz, h3]