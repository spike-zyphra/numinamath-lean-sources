import Mathlib

theorem algebra_254931 :
  { (a, b, c) : ℤ × ℤ × ℤ | 
    a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧
    -- 等比数列条件
    b^2 = a * c ∧ 
    -- 三项和为105
    a + b + c = 105 ∧
    -- 从第三项减去15后得到等差数列
    2 * b = a + c - 15
  } = { (15, 30, 60), (60, 30, 15) } := by
  ext ⟨a, b, c⟩
  simp
  constructor
  · -- Assume (a, b, c) in the left side set, prove it is in the right side set.
    rintro ⟨ha, hb, hc, h1, h2, h3⟩
    have h4 : b = 30 := by
      nlinarith
    have h5 : a + c = 75 := by 
      rw [h4] at h3
      linarith
    have h6 : a * c = 900 := by
      rw [h4] at h1
      nlinarith
    have h8 : a = 15 ∨ a = 60 := by
      have h9 : a^2 - 75 * a + 900 = 0 := by
        have h10 : c = 75 - a := by linarith [h5]
        rw [h10] at h6
        linarith
      have h11 : (a - 15) * (a - 60) = 0 := by 
        nlinarith
      cases' (mul_eq_zero.mp h11) with h12 h13
      · 
        left 
        linarith
      · 
        right 
        linarith
    cases' h8 with ha15 ha60
    · 
      -- Case a = 15
      have hc15 : c = 60 := by 
        nlinarith [ha15, h5]
      simp [ha15, h4, hc15]
    · 
      -- Case a = 60
      have hc60 : c = 15 := by 
        nlinarith [ha60, h5]
      simp [ha60, h4, hc60]
  · -- Assume (a, b, c) in the right side set, prove it is in the left side set.
    rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      · norm_num 
    · 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      · norm_num