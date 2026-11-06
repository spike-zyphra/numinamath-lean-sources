import Mathlib

theorem number_theory_51784 :
    {(x, y, z) : ℤ × ℤ × ℤ | x + y * z = 2 ∧ y + x * z = 2 ∧ z + x * y = 2} =
    {(1, 1, 1), (-2, -2, -2)} := by
  ext ⟨x, y, z⟩
  simp
  constructor
  · -- Assume (x,y,z) is in the left side, prove it's in the right
    rintro ⟨h1, h2, h3⟩
    have h4 : (x - y) * (1 - z) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h4) with h5 h6
    · -- Case where x - y = 0, so x = y
      have h7 : x = y := by linarith
      have h8 : x * (1 + z) = 2 := by
        have h9 : x + y * z = 2 := h1
        rw [show y = x by linarith [h7] ] at h9
        nlinarith
      have h9 : z = 2 - x^2 := by
        have h10 : z + x * y = 2 := h3
        rw [show y = x by linarith [h7] ] at h10
        nlinarith
      rw [h9] at h8
      have h11 : x^3 - 3 * x + 2 = 0 := by
        nlinarith
      have h12 : (x - 1) ^ 2 * (x + 2) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h12) with h13 h14
      · -- Case where (x - 1) ^ 2 = 0, so x = 1
        have hx1 : x = 1 := by nlinarith
        have hy1 : y = 1 := by linarith [h7, hx1]
        have hz1 : z = 1 := by nlinarith [h9, hx1]
        simp [hx1, hy1, hz1]
      · -- Case where x + 2 = 0, so x = -2
        have hx2 : x = -2 := by nlinarith
        have hy2 : y = -2 := by linarith [h7, hx2]
        have hz2 : z = -2 := by nlinarith [h9, hx2]
        simp [hx2, hy2, hz2]
    · -- Case where 1 - z = 0, so z = 1
      have h10 : z = 1 := by linarith
      rw [h10] at h1 h2 h3
      have h11 : x + y = 2 := by
        nlinarith
      have h12 : x * y = 1 := by
        nlinarith
      have hx1 : x = 1 := by 
        have h13 : x ≤ 1 := by nlinarith [show x * y = 1 from h12]
        have h14 : x ≥ 1 := by nlinarith [show x * y = 1 from h12]
        interval_cases x <;> omega
      have hy1 : y = 1 := by 
        nlinarith
      simp [hx1, hy1, h10]
  · -- Show the right side is contained in the left
    rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · -- Check (1, 1, 1)
      constructor
      · -- 1 + 1 * 1 = 2
        norm_num
      constructor
      · -- 1 + 1 * 1 = 2
        norm_num
      · -- 1 + 1 * 1 = 2
        norm_num
    · -- Check (-2, -2, -2)
      constructor
      · -- -2 + (-2) * (-2) = 2
        norm_num
      constructor
      · -- -2 + (-2) * (-2) = 2
        norm_num
      · -- -2 + (-2) * (-2) = 2
        norm_num