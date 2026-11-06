import Mathlib

open Real

theorem algebra_87894 :
  {(x, y, z) : ℝ × ℝ × ℝ | x^2 + y * z = 1 ∧ y^2 - x * z = 0 ∧ z^2 + x * y = 1} =
  {(√2 / 2, √2 / 2, √2 / 2), (-√2 / 2, -√2 / 2, -√2 / 2)}:= by
  ext ⟨x,y,z⟩
  simp [-one_div]
  constructor
  · 
    rintro ⟨h1, h2, h3⟩
    have h5 : x = z ∨ x + z - y = 0 := by 
      have eq1 : (x - z) * (x + z - y) = 0 := by
        nlinarith
      cases (mul_eq_zero.mp eq1) with
      | inl h9 =>
        left
        linarith
      | inr h10 =>
        right
        linarith
    cases h5 with
    | inl h2l =>
      have h9 : x = z := h2l
      have h22 : y^2 = x^2 := by 
        rw [show z = x by linarith [h9]] at h2
        nlinarith
      have h7 : y = x ∨ y = -x := by
        have h9 : y^2 = x^2 := h22
        have : y = x ∨ y = -x := by 
          rw [sq_eq_sq_iff_eq_or_eq_neg] at h9
          tauto
        assumption
      cases h7 with
      | inl hyx =>
        have h9 : y = x := by linarith
        have h10 : z = x := by linarith [h9, h9]
        rw [show y = x by linarith, show z = x by linarith] at h1 h3
        have h11 : 2 * x^2 = 1 := by nlinarith
        have h12 : x^2 = 1 / 2 := by nlinarith
        have h21 : x = Real.sqrt (1 / 2) ∨ x = -Real.sqrt (1 / 2) := by
          have h13 : x^2 - (1 / 2) = 0 := by
            linarith
          have h14 : x^2 - (1 / 2) = (x - Real.sqrt (1 / 2)) * (x + Real.sqrt (1 / 2)) := by
            ring_nf
            rw [Real.sq_sqrt (by norm_num)]
            linarith
          rw [h14] at h13
          cases (mul_eq_zero.mp h13) with
          | inl h15 =>
            left
            linarith
          | inr h16 =>
            right
            linarith
        cases h21 with
        | inl h21l =>
          have h21l1 : x = Real.sqrt (2) / 2 := by
            have h27 : Real.sqrt (1 / 2) = Real.sqrt (2) / 2 := by
              rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num <;> ring_nf <;> norm_num
            rw [h27] at h21l
            linarith
          have h24 : y = Real.sqrt (2) / 2 := by
            rw [show y = x by linarith, h21l1]
          have h25 : z = Real.sqrt (2) / 2 := by
            rw [show z = x by linarith, h21l1]
          simp [h21l1, h24, h25]
        | inr h21r =>
          have h21r1 : x = -Real.sqrt (2) / 2 := by
            have h27 : Real.sqrt (1 / 2) = Real.sqrt (2) / 2 := by
              rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num <;> ring_nf <;> norm_num
            rw [h27] at h21r
            linarith
          have h24 : y = -Real.sqrt (2) / 2 := by
            rw [show y = x by linarith, h21r1]
          have h25 : z = -Real.sqrt (2) / 2 := by
            rw [show z = x by linarith, h21r1]
          simp [h21r1, h24, h25]
      | inr hyx =>
        have h9 : y = -x := by linarith
        have h10 : z = x := by linarith [h2l, h9]
        rw [show y = -x by linarith, show z = x by linarith] at h1 h3
        nlinarith
    | inr h5r =>
      have h6 : y = x + z := by linarith
      rw [h6] at h2
      have h7 : x^2 + x * z + z^2 = 0 := by
        nlinarith [sq_nonneg (x + z)]
      have h8 : (x + z) ^ 2 + z^2 = 0 := by
        nlinarith
      have h9 : (x + z) ^ 2 = 0 := by
        linarith [sq_nonneg (x + z), sq_nonneg z]
      have h10 : x + z = 0 := by
        nlinarith
      have h11 : z ^ 2 = 0 := by
        linarith [sq_nonneg (x + z), sq_nonneg z]
      have h12 : z = 0 := by
        nlinarith
      have h13 : x = 0 := by 
        nlinarith
      have h14 : y = 0 := by 
        linarith [h6, h13, h12]
      rw [h13, h14, h12] at h1
      nlinarith
  · 
    rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · 
      constructor
      · 
        have h1 : Real.sqrt 2 ^ 2 = 2 := by 
          norm_num [Real.sq_sqrt]
        nlinarith [h1, Real.sqrt_nonneg 2, Real.sqrt_nonneg 2, Real.sqrt_nonneg 2]
      constructor
      · 
        have h1 : Real.sqrt 2 ^ 2 = 2 := by 
          norm_num [Real.sq_sqrt]
        nlinarith [h1, Real.sqrt_nonneg 2, Real.sqrt_nonneg 2, Real.sqrt_nonneg 2]
      · 
        have h1 : Real.sqrt 2 ^ 2 = 2 := by 
          norm_num [Real.sq_sqrt]
        nlinarith [h1, Real.sqrt_nonneg 2, Real.sqrt_nonneg 2, Real.sqrt_nonneg 2]
    · 
      constructor
      · -- First equation: x^2 + y * z = 1
        have h1 : Real.sqrt 2 ^ 2 = 2 := by 
          norm_num [Real.sq_sqrt]
        nlinarith [h1, Real.sqrt_nonneg 2, Real.sqrt_nonneg 2, Real.sqrt_nonneg 2]
      constructor
      · -- Second equation: y^2 - x * z = 0
        have h1 : Real.sqrt 2 ^ 2 = 2 := by 
          norm_num [Real.sq_sqrt]
        nlinarith [h1, Real.sqrt_nonneg 2, Real.sqrt_nonneg 2, Real.sqrt_nonneg 2]
      · -- Third equation: z^2 + x * y = 1
        have h1 : Real.sqrt 2 ^ 2 = 2 := by 
          norm_num [Real.sq_sqrt]
        nlinarith [h1, Real.sqrt_nonneg 2, Real.sqrt_nonneg 2, Real.sqrt_nonneg 2]