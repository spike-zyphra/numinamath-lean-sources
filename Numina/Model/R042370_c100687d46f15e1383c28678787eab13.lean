import Mathlib

theorem algebra_291217 :
  {(q, d) : ℝ × ℝ | 
    -- 最后一项相等
    1 + 7 * d = 1 * q^3 ∧ 
    -- 几何数列的和比等差数列最后一项大21
    1 + q + q^2 + q^3 = 1 + 7 * d + 21} =
  {(4, 9), (-5, -18)} := by
  ext ⟨q, d⟩
  simp
  constructor
  · -- Assume both equations hold, prove pair is in the set
    rintro ⟨h1, h2⟩
    have h3 : q^2 + q - 20 = 0 := by 
      nlinarith [sq_nonneg (q + 4), sq_nonneg (q - 4), sq_nonneg (d + 18), sq_nonneg (d - 9) ]
    have h4 : (q - 4) * (q + 5) = 0 := by
      nlinarith [h3]
    cases' (mul_eq_zero.mp h4) with hq4 hq5
    · -- Case q = 4
      have hq4' : q = 4 := by linarith 
      have hd9 : d = 9 := by
        rw [hq4'] at h1
        nlinarith
      left
      exact ⟨hq4', hd9⟩
    · -- Case q = -5
      have hq5' : q = -5 := by linarith 
      have hd18 : d = -18 := by
        rw [hq5'] at h1
        nlinarith
      right
      exact ⟨hq5', hd18⟩
  · -- Show the pairs in the set satisfy both equations
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- First pair (4, 9)
      constructor
      · norm_num
      · norm_num
    · -- Second pair (-5, -18)
      constructor
      · norm_num
      · norm_num