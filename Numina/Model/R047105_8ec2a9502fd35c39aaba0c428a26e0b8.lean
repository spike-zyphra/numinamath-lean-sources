import Mathlib


theorem algebra_610157 : {(x, y, z) : ℝ × ℝ × ℝ | x ^ 2 * y + y ^ 2 * z = 1040 ∧ x ^ 2 * z + z ^ 2 * y = 260 ∧ (x - y) * (y - z) * (z - x) = -540} = {(16, 4, 1), (1, 16, 4)} := by

  ext ⟨x, y, z⟩
  simp [-one_div]
  constructor
  · -- Assume the system of equations is satisfied; prove (x,y,z) = (16,4,1) or (1,16,4).
    rintro ⟨h₁, h₂, h₃⟩
    have h₃' : (y - 4 * z) * (x ^ 2 + y * z) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h₃') with h₃₀ h₃₁
    · -- When $y = 4z$, solve the system of equations.
      have h₃₀' : y = 4 * z := by linarith
      rw [h₃₀'] at h₁ h₂ h₃
      have eq1 : x ^ 2 * z + 4 * z ^ 3 = 260 := by
        nlinarith
      have eq3 : (x - 4 * z) * (3 * z) * (z - x) = -540 := by
        nlinarith
      have h6 : z ≠ 0 := by
        by_contra h
        rw [h] at eq1 eq3
        nlinarith
      have eq5 : z ^ 2 * x = 16 := by
        nlinarith [sq_pos_of_ne_zero (show z ≠ 0 by assumption)]
      have h7 : z ^ 3 =1 ∨ z ^ 3 =64 := by
        have eq8 : x =16 / (z ^ 2) := by
          field_simp
          nlinarith
        rw [eq8] at eq1
        have eq9 : (z ^ 3 -1) * (z ^ 3 - 64) =0 := by
          field_simp at eq1 ⊢
          nlinarith [sq_pos_of_ne_zero (show z ≠ 0 by assumption)]
        cases' (mul_eq_zero.mp eq9) with h10 h10
        · left
          linarith
        · right
          linarith
      cases h7 with
      | inl h14 =>
        have h15 : z =1 := by
          have h15 : z^3=1 := by
            linarith
          have h16 : z^3-1=0 := by
            nlinarith
          have h17 : (z-1)*(z^2+z+1)=0 := by
            nlinarith
          cases' (mul_eq_zero.mp h17) with h18 h19
          · -- h18 =z-1=0
            linarith
          · -- h19=z^2+z+1=0
            nlinarith [sq_nonneg (z + 0.5)]
        have h17 : x =16 := by
          rw [show z =1 by linarith] at eq5
          nlinarith
        left
        simp [Prod.ext_iff, h17, show y = 4 by nlinarith, show z =1 by nlinarith]
      | inr h14 =>
        have h15 : z =4 := by
          have h15 : z^3=64 := by
            linarith
          have h16 : z^3-64=0 := by
            nlinarith
          have h17 : (z-4)*(z^2+4*z+16)=0 := by
            nlinarith
          cases' (mul_eq_zero.mp h17) with h18 h19
          · -- h18 =z-4=0
            linarith
          · -- h19=z^2+4*z+16=0
            nlinarith [sq_nonneg (z + 2)]
        have h17 : x =1 := by
          rw [show z =4 by nlinarith] at eq5
          nlinarith
        right
        simp [Prod.ext_iff, h17, show y = 16 by nlinarith, show z =4 by nlinarith]
    · -- When $x^2 + y z = 0$.
      exfalso
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        sq_nonneg (x + 16), sq_nonneg (y + 16), sq_nonneg (z + 16),
        sq_nonneg (x - 16), sq_nonneg (y - 16), sq_nonneg (z - 16)
      ]
  · -- Assume (x,y,z) = (16,4,1) or (1,16,4); prove the system of equations.
    rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · constructor
      · norm_num
      constructor
      · norm_num
      · norm_num