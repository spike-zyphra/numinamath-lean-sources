import Mathlib

theorem algebra_255236 :
  { (x, y, z) : ℝ × ℝ × ℝ | 
    x + y + z = 12 ∧ 
    x^2 + y^2 + z^2 = 230 ∧
    x * y = -15 
  } = { (15, -1, -2), (-1, 15, -2), (3, -5, 14), (-5, 3, 14) } := by
  ext ⟨x, y, z⟩
  simp
  constructor
  · -- Assume (x, y, z) satisfies all three equations
    rintro ⟨h₁, h₂, h₃⟩
    have h4 : z = 12 - x - y := by 
      linarith 
    rw [h4] at h₂ 
    have h5 : (x + y) ^ 2 - 12 * (x + y) - 28 = 0 := by
      nlinarith
    have h6 : (x + y - 14) * (x + y + 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h6) with h7 h8
    · -- x + y = 14
      have h9 : x + y = 14 := by 
        linarith 
      have h10 : z = -2 := by 
        nlinarith [h4, h9] 
      have h11 : (x - 15) * (x + 1) = 0 := by
        have h9 : x + y = 14 := by 
          linarith 
        have h12 : y = 14 - x := by 
          linarith 
        rw [h12] at h₃ 
        nlinarith
      cases' (mul_eq_zero.1 h11) with h12 h13 
      · -- x = 15 
        have hx : x = 15 := by 
          linarith 
        have hy : y = -1 := by 
          nlinarith [h9, hx] 
        have hz : z = -2 := by 
          linarith 
        simp [hx, hy, hz]
      · -- x = -1 
        have hx : x = -1 := by 
          linarith 
        have hy : y = 15 := by 
          nlinarith [h9, hx] 
        have hz : z = -2 := by 
          linarith 
        simp [hx, hy, hz]
    · -- x + y = -2 
      have h9 : x + y = -2 := by 
        linarith 
      have h10 : z = 14 := by 
        nlinarith [h4, h9] 
      have h11 : (x - 3) * (x + 5) = 0 := by 
        have h9 : x + y = -2 := by 
          linarith 
        have h12 : y = -2 - x := by 
          linarith 
        rw [h12] at h₃ 
        nlinarith 
      cases' (mul_eq_zero.1 h11) with h13 h14 
      · -- x = 3 
        have hx : x = 3 := by 
          linarith 
        have hy : y = -5 := by 
          nlinarith [h9, hx] 
        have hz : z = 14 := by 
          linarith 
        simp [hx, hy, hz]
      · -- x = -5 
        have hx : x = -5 := by 
          linarith 
        have hy : y = 3 := by 
          nlinarith [h9, hx] 
        have hz : z = 14 := by 
          linarith 
        simp [hx, hy, hz]
  · -- Show that each of the four points satisfies the system
    rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · -- Check (15, -1, -2)
      constructor 
      · -- x + y + z = 12 
        norm_num 
      constructor 
      · -- x^2 + y^2 + z^2 = 230 
        norm_num 
      · -- x * y = -15 
        norm_num
    · -- Check (-1, 15, -2)
      constructor 
      · -- x + y + z = 12 
        norm_num 
      constructor 
      · -- x^2 + y^2 + z^2 = 230 
        norm_num 
      · -- x * y = -15 
        norm_num
    · -- Check (3, -5, 14)
      constructor 
      · -- x + y + z = 12 
        norm_num 
      constructor 
      · -- x^2 + y^2 + z^2 = 230 
        norm_num 
      · -- x * y = -15 
        norm_num
    · -- Check (-5, 3, 14)
      constructor 
      · -- x + y + z = 12 
        norm_num 
      constructor 
      · -- x^2 + y^2 + z^2 = 230 
        norm_num 
      · -- x * y = -15 
        norm_num