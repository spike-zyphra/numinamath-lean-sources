import Mathlib

theorem algebra_155158 (x y z : ℝ) :
    x^2 + y^4 + z^6 + 14 = 2 * x + 4 * y^2 + 6 * z^3 ↔
    (x = 1 ∧ y = Real.sqrt 2 ∧ z = 3 ^ ((1 : ℝ) / 3)) ∨
    (x = 1 ∧ y = -Real.sqrt 2 ∧ z = 3 ^ ((1 : ℝ) / 3)) := by
  constructor
  · -- Forward direction
    intro h
    have h1 : (x - 1) ^ 2 + (y^2 - 2) ^ 2 + (z^3 - 3) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y^2 - 2), sq_nonneg (z^3 - 3),
          sq_nonneg (y ^ 2 - 2), sq_nonneg (z^3 - 3), sq_nonneg (x - 1)]
    have hx1 : (x - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y^2 - 2), sq_nonneg (z^3 - 3)]
    have hy2 : (y^2 - 2) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y^2 - 2), sq_nonneg (z^3 - 3)]
    have hz3 : (z^3 - 3) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y^2 - 2), sq_nonneg (z^3 - 3)]
    have hx_eq : x = 1 := by
      nlinarith [hx1]
    have hy_eq : y^2 = 2 := by
      nlinarith [hy2]
    have hz_eq1 : z^3 = 3 := by
      nlinarith [hz3]
    have hz_eq2 : z = (3 : ℝ) ^ ((1 : ℝ) / 3) := by
      have h3_pos : z > 0 := by
        nlinarith [sq_nonneg (z ^ 3 - 3), sq_nonneg (z ^ 3), sq_nonneg (z), hz_eq1]
      have h3_eq : z^3 = 3 := by
        nlinarith [hz_eq1]
      have h4 : z = (3 : ℝ) ^ ((1 : ℝ) / 3) := by
        have h5 : (z ^ 3) = 3 := by
          nlinarith [hz_eq1]
        have h6 : z > 0 := by
          nlinarith [sq_nonneg (z ^ 3 - 3), sq_nonneg (z ^ 3), sq_nonneg (z), hz_eq1]
        have h7 : ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = 3 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          norm_num
          all_goals linarith
        have h8 : z = ((3 : ℝ) ^ ((1 : ℝ) / 3)) := by
          have h9 : ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = 3 := by
            nlinarith [Real.rpow_pos_of_pos (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
          have h10 : z ^ 3 = 3 := by
            nlinarith [hz_eq1]
          have h11 : ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = z ^ 3 := by
            rw [h9, h10]
          have h12 : ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3) := by
            rfl
          have h13 : ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = z ^ 3 := by
            linarith [h11, h12]
          have h14 : ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = z ^ 3 := by
            linarith [h11, h12]
          have h15 : (z - ((3 : ℝ) ^ ((1 : ℝ) / 3))) * (z ^ 2 + z * ((3 : ℝ) ^ ((1 : ℝ) / 3)) + ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2) = 0 := by
            nlinarith [h14, sq_nonneg (z - ((3 : ℝ) ^ ((1 : ℝ) / 3))), sq_nonneg (z + ((3 : ℝ) ^ ((1 : ℝ) / 3)))]
          cases (mul_eq_zero.mp h15) with
          | inl h_i =>
            linarith
          | inr h_j =>
            have h16 : z ^ 2 + z * ((3 : ℝ) ^ ((1 : ℝ) / 3)) + ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 = 0 := by
              linarith
            have h17 : z ^ 2 + z * ((3 : ℝ) ^ ((1 : ℝ) / 3)) + ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 > 0 := by
              nlinarith [sq_nonneg (z + ((3 : ℝ) ^ ((1 : ℝ) / 3)) / 2), sq_nonneg (z - ((3 : ℝ) ^ ((1 : ℝ) / 3)) / 2), sq_nonneg ((3 : ℝ) ^ ((1 : ℝ) / 3)), sq_nonneg (z)]
            linarith [h16, h17]
        exact h8
      exact h4
    have hy_eq1 : y = Real.sqrt 2 ∨ y = -Real.sqrt 2 := by
      have h2 : y^2 = 2 := by
        nlinarith [hy_eq]
      have h3 : (y - Real.sqrt 2) * (y + Real.sqrt 2) = 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      cases (mul_eq_zero.mp h3) with
      | inl h7 =>
        left
        linarith
      | inr h8 =>
        right
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    cases hy_eq1 with
    | inl h_y =>
      left
      exact ⟨hx_eq, h_y, hz_eq2⟩
    | inr h_y =>
      right
      exact ⟨hx_eq, h_y, hz_eq2⟩
  · -- Backward direction
    rintro (h | h)
    · -- First case
      rcases h with ⟨hx, hy, hz⟩
      rw [hx, hy, hz]
      have h3 : ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = 3 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals linarith
      have h4 : ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 6 = 9 := by
        calc
          ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 6 = (((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3) ^ 2 := by ring
          _ = 3 ^ 2 := by rw [h3]
          _ = 9 := by norm_num
      have hy2 : (Real.sqrt 2) ^ 2 = 2 := by
        exact Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
      have hy4 : (Real.sqrt 2) ^ 4 = 4 := by
        calc
          (Real.sqrt 2) ^ 4 = ((Real.sqrt 2) ^ 2) ^ 2 := by ring
          _ = 2 ^ 2 := by rw [hy2]
          _ = 4 := by norm_num
      nlinarith [h4, hy4, h3, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    · -- Second case
      rcases h with ⟨hx, hy, hz⟩
      rw [hx, hy, hz]
      have h3 : ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = 3 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals linarith
      have h4 : ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 6 = 9 := by
        calc
          ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 6 = (((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3) ^ 2 := by ring
          _ = 3 ^ 2 := by rw [h3]
          _ = 9 := by norm_num
      have hy2 : (-Real.sqrt 2) ^ 2 = 2 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      have hy4 : (-Real.sqrt 2) ^ 4 = 4 := by
        calc
          (-Real.sqrt 2) ^ 4 = ((-Real.sqrt 2) ^ 2) ^ 2 := by ring
          _ = 2 ^ 2 := by rw [hy2]
          _ = 4 := by norm_num
      nlinarith [h4, hy4, h3, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]