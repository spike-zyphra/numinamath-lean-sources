import Mathlib

theorem algebra_197491 (a : ℝ) :
    {(x, y, z) : ℝ × ℝ × ℝ | x + y + z = a ∧ x^2 + y^2 + z^2 = a^2 ∧ x^3 + y^3 + z^3 = a^3} = {(a, 0, 0), (0, a, 0), (0, 0, a)} := by
  ext ⟨x, y, z⟩
  simp
  constructor
  · -- Assume (x, y, z) satisfy all three equations, prove (x, y, z) ∈ {(a, 0, 0), (0, a, 0), (0, 0, a)}
    rintro ⟨h1, h2, h3⟩
    have h4 : x * y + y * z + z * x = 0 := by
      have h4 : x^2 + y^2 + z^2 = (x + y + z) ^ 2 - 2 * (x * y + y * z + z * x) := by
        ring
      rw [h1] at h4
      linarith
    have h5 : x * y * z = 0 := by
      have h6 : x^3 + y^3 + z^3 = (x + y + z) ^ 3 - 3 * (x + y + z) * (x * y + y * z + z * x) + 3 * (x * y * z) := by
        ring
      rw [h1, h4] at h6
      linarith [h3, h6]
    have h6 : x = 0 ∨ y = 0 ∨ z = 0 := by
      cases (mul_eq_zero.mp h5) with
      | inl h7 =>
        cases (mul_eq_zero.mp h7) with
        | inl h8 =>
          left
          tauto
        | inr h9 =>
          right
          left
          tauto
      | inr h8 =>
        right
        right
        tauto
    rcases h6 with (h6 | h6 | h6)
    · 
      have h7 : y + z = a := by
        rw [h6] at h1
        linarith
      have h8 : y * z = 0 := by
        rw [h6] at h4
        linarith
      cases' (mul_eq_zero.mp h8) with h9 h10
      · 
        have h11 : z = a := by
          nlinarith
        have h10 : y = 0 := by
          linarith
        simp [h6, h10, h11]
      · 
        have h9 : y = a := by
          nlinarith
        have h11 : z = 0 := by
          linarith
        simp [h6, h9, h11]
    · 
      have h7 : x + z = a := by
        rw [h6] at h1
        linarith
      have h8 : x * z = 0 := by
        rw [h6] at h4
        linarith
      cases' (mul_eq_zero.mp h8) with h9 h10
      · 
        have h11 : z = a := by
          nlinarith
        have h10 : x = 0 := by
          linarith
        simp [h6, h10, h11]
      · 
        have h9 : x = a := by
          nlinarith
        have h11 : z = 0 := by
          linarith
        simp [h6, h9, h11]
    · 
      have h7 : x + y = a := by
        rw [h6] at h1
        linarith
      have h8 : x * y = 0 := by
        rw [h6] at h4
        linarith
      cases' (mul_eq_zero.mp h8) with h9 h10
      · 
        have h11 : y = a := by
          nlinarith
        have h10 : x = 0 := by
          linarith
        simp [h6, h10, h11]
      · 
        have h9 : x = a := by
          nlinarith
        have h11 : y = 0 := by
          linarith
        simp [h6, h9, h11]
  · -- Assume (x, y, z) ∈ {(a, 0, 0), (0, a, 0), (0, 0, a)}, prove (x, y, z) satisfy all three equations
    rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · 
      constructor
      · 
        norm_num
      constructor
      · 
        norm_num
      · 
        norm_num
    · 
      constructor
      · 
        norm_num
      constructor
      · 
        norm_num
      · 
        norm_num
    · 
      constructor
      · 
        norm_num
      constructor
      · 
        norm_num
      · 
        norm_num