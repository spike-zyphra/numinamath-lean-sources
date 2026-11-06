import Mathlib

  theorem algebra_105074 :
    {(a, b, c) : ℝ × ℝ × ℝ | a + b = 8 ∧ a^2 + b^2 + c^2 = 32} = {(4, 4, 0)} := by
  ext ⟨a, b, c⟩
  simp [-zero_div]
  constructor
  · -- First prove the forward direction: if (a, b, c) is a solution, then (4, 4, 0)
    rintro ⟨h1, h2⟩
    have h3 : b = 8 - a := by linarith
    rw [h3] at h2
    have h4 : 2 * (a - 4)^2 + c^2 = 0 := by
      nlinarith
    have ha1 : (a - 4)^2 = 0 := by
      nlinarith [sq_nonneg (a - 4), sq_nonneg c]
    have ha2 : a = 4 := by
      nlinarith
    have hb2 : b = 4 := by
      rw [ha2] at h3
      linarith
    have hc1 : c^2 = 0 := by
      nlinarith [sq_nonneg (a - 4), sq_nonneg c, ha1]
    have hc2 : c = 0 := by
      nlinarith
    simp [ha2, hb2, hc2]
  · -- Now prove the reverse direction: (4, 4, 0) is a solution
    rintro ⟨rfl, rfl, rfl⟩
    constructor
    · norm_num
    · norm_num