import Mathlib

theorem algebra_199833 :
    {x : ℝ | 3 * x ^ 5 + 3 * x ^ 4 + 2 * x ^ 3 + 2 * x ^ 2 - x - 1 = 0 ∧
    3 * x ^ 5 - 3 * x ^ 4 + 2 * x ^ 3 - 2 * x ^ 2 - x + 1 = 0} = {1 / √3, -1 / √3} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume x satisfies both equations
    rintro ⟨h1, h2⟩
    have h3 : 3 * x ^ 4 + 2 * x ^ 2 - 1 = 0 := by
      nlinarith
    have h4 : (3 * x ^ 2 - 1) * (x ^ 2 + 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h4) with h41 h42
    · -- Assume 3x^2 - 1 = 0
      have hx2 : x ^ 2 = 1 / 3 := by linarith 
      have h5 : x = Real.sqrt (1 / 3) ∨ x = -Real.sqrt (1 / 3) := by 
        apply eq_or_eq_neg_of_sq_eq_sq
        norm_num
        linarith
      cases h5 with
      | inl h7 =>
        have h8 : x = 1 / Real.sqrt 3 := by 
          have h7' : x = Real.sqrt (1 / 3) := h7 
          have h9 : Real.sqrt (1 / 3) = 1 / Real.sqrt 3 := by 
            field_simp [Real.sqrt_eq_iff_sq_eq]
            all_goals norm_num
          rw [h9] at h7'
          assumption
        left
        exact h8
      | inr h7 =>
        have h7' : x = -Real.sqrt (1 / 3) := h7 
        have h9 : Real.sqrt (1 / 3) = 1 / Real.sqrt 3 := by 
          field_simp [Real.sqrt_eq_iff_sq_eq]
          all_goals norm_num
        have h10 : x = - (1 / Real.sqrt 3) := by 
          rw [h9] at h7' 
          linarith 
        have h8 : x = -1 / Real.sqrt 3 := by 
          rw [show x = - (1 / Real.sqrt 3) by linarith [h10]]
          <;> ring
        right
        exact h8
    · -- Assume x^2 + 1 = 0 
      have h5 : x ^ 2 + 1 = 0 := by linarith 
      have h6 : x ^ 2 = -1 := by linarith 
      have h7 : x ^ 2 ≥ 0 := sq_nonneg x 
      nlinarith 
  · -- Show that 1/√3 and -1/√3 satisfy both equations 
    rintro (h | h)
    · -- Assume x = 1 / √3 
      rw [h] 
      constructor 
      · -- Verify the first equation 
        have h11 : Real.sqrt 3 > 0 := by 
          apply Real.sqrt_pos.2 
          all_goals norm_num 
        have h11' : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
        have h12 : (1 / Real.sqrt 3 : ℝ) ^ 2 = 1 / 3 := by 
          field_simp [h11']
        have h13 : (1 / Real.sqrt 3 : ℝ) ^ 3 = 1 / (3 * Real.sqrt 3) := by 
          field_simp [h11']
          <;> nlinarith [Real.sqrt_nonneg 3, Real.sqrt_pos.2 (show (0 : ℝ) < 3 by norm_num)]
        have h14 : (1 / Real.sqrt 3 : ℝ) ^ 4 = 1 / 9 := by 
          calc 
            (1 / Real.sqrt 3 : ℝ) ^ 4 = ((1 / Real.sqrt 3 : ℝ) ^ 2) ^ 2 := by ring 
            _ = (1 / 3) ^ 2 := by rw [h12]
            _ = 1 / 9 := by norm_num 
        have h15 : (1 / Real.sqrt 3 : ℝ) ^ 5 = 1 / (9 * Real.sqrt 3) := by 
          calc 
            (1 / Real.sqrt 3 : ℝ) ^ 5 = (1 / Real.sqrt 3) * (1 / Real.sqrt 3) ^ 4 := by ring 
            _ = (1 / Real.sqrt 3) * (1 / 9) := by rw [h14]
            _ = 1 / (9 * Real.sqrt 3) := by 
              field_simp [h11']
              <;> nlinarith [Real.sqrt_nonneg 3, Real.sqrt_pos.2 (show (0 : ℝ) < 3 by norm_num)]
        simp only [h12, h13, h14, h15] 
        field_simp [h11']
        <;> nlinarith [Real.sqrt_nonneg 3, Real.sqrt_pos.2 (show (0 : ℝ) < 3 by norm_num)]
      · -- Verify the second equation 
        have h11 : Real.sqrt 3 > 0 := by 
          apply Real.sqrt_pos.2 
          all_goals norm_num 
        have h11' : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
        have h12 : (1 / Real.sqrt 3 : ℝ) ^ 2 = 1 / 3 := by 
          field_simp [h11']
        have h13 : (1 / Real.sqrt 3 : ℝ) ^ 3 = 1 / (3 * Real.sqrt 3) := by 
          field_simp [h11']
          <;> nlinarith [Real.sqrt_nonneg 3, Real.sqrt_pos.2 (show (0 : ℝ) < 3 by norm_num)]
        have h14 : (1 / Real.sqrt 3 : ℝ) ^ 4 = 1 / 9 := by 
          calc 
            (1 / Real.sqrt 3 : ℝ) ^ 4 = ((1 / Real.sqrt 3 : ℝ) ^ 2) ^ 2 := by ring 
            _ = (1 / 3) ^ 2 := by rw [h12]
            _ = 1 / 9 := by norm_num 
        have h15 : (1 / Real.sqrt 3 : ℝ) ^ 5 = 1 / (9 * Real.sqrt 3) := by 
          calc 
            (1 / Real.sqrt 3 : ℝ) ^ 5 = (1 / Real.sqrt 3) * (1 / Real.sqrt 3) ^ 4 := by ring 
            _ = (1 / Real.sqrt 3) * (1 / 9) := by rw [h14]
            _ = 1 / (9 * Real.sqrt 3) := by 
              field_simp [h11']
              <;> nlinarith [Real.sqrt_nonneg 3, Real.sqrt_pos.2 (show (0 : ℝ) < 3 by norm_num)]
        simp only [h12, h13, h14, h15] 
        field_simp [h11']
        <;> nlinarith [Real.sqrt_nonneg 3, Real.sqrt_pos.2 (show (0 : ℝ) < 3 by norm_num)]
    · -- Assume x = -1 / √3 
      rw [h] 
      constructor 
      · -- Verify the first equation 
        have h11 : Real.sqrt 3 > 0 := by 
          apply Real.sqrt_pos.2 
          all_goals norm_num 
        have h11' : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
        have h12 : (-1 / Real.sqrt 3 : ℝ) ^ 2 = 1 / 3 := by 
          have h2 : Real.sqrt 3 ^ 2 = 3 := h11'
          field_simp [h2]
        have h13 : (-1 / Real.sqrt 3 : ℝ) ^ 3 = -1 / (3 * Real.sqrt 3) := by 
          field_simp [h11']
          <;> nlinarith [Real.sqrt_nonneg 3, Real.sqrt_pos.2 (show (0 : ℝ) < 3 by norm_num)]
        have h14 : (-1 / Real.sqrt 3 : ℝ) ^ 4 = 1 / 9 := by 
          calc 
            (-1 / Real.sqrt 3 : ℝ) ^ 4 = ((-1 / Real.sqrt 3 : ℝ) ^ 2) ^ 2 := by ring 
            _ = (1 / 3) ^ 2 := by rw [h12]
            _ = 1 / 9 := by norm_num 
        have h15 : (-1 / Real.sqrt 3 : ℝ) ^ 5 = -1 / (9 * Real.sqrt 3) := by 
          calc 
            (-1 / Real.sqrt 3 : ℝ) ^ 5 = (-1 / Real.sqrt 3) * (-1 / Real.sqrt 3) ^ 4 := by ring 
            _ = (-1 / Real.sqrt 3) * (1 / 9) := by rw [h14]
            _ = -1 / (9 * Real.sqrt 3) := by 
              field_simp [h11']
              <;> nlinarith [Real.sqrt_nonneg 3, Real.sqrt_pos.2 (show (0 : ℝ) < 3 by norm_num)]
        simp only [h12, h13, h14, h15] 
        field_simp [h11']
        <;> nlinarith [Real.sqrt_nonneg 3, Real.sqrt_pos.2 (show (0 : ℝ) < 3 by norm_num)]
      · -- Verify the second equation 
        have h11 : Real.sqrt 3 > 0 := by 
          apply Real.sqrt_pos.2 
          all_goals norm_num 
        have h11' : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
        have h12 : (-1 / Real.sqrt 3 : ℝ) ^ 2 = 1 / 3 := by 
          have h2 : Real.sqrt 3 ^ 2 = 3 := h11'
          field_simp [h2]
        have h13 : (-1 / Real.sqrt 3 : ℝ) ^ 3 = -1 / (3 * Real.sqrt 3) := by 
          field_simp [h11']
          <;> nlinarith [Real.sqrt_nonneg 3, Real.sqrt_pos.2 (show (0 : ℝ) < 3 by norm_num)]
        have h14 : (-1 / Real.sqrt 3 : ℝ) ^ 4 = 1 / 9 := by 
          calc 
            (-1 / Real.sqrt 3 : ℝ) ^ 4 = ((-1 / Real.sqrt 3 : ℝ) ^ 2) ^ 2 := by ring 
            _ = (1 / 3) ^ 2 := by rw [h12]
            _ = 1 / 9 := by norm_num 
        have h15 : (-1 / Real.sqrt 3 : ℝ) ^ 5 = -1 / (9 * Real.sqrt 3) := by 
          calc 
            (-1 / Real.sqrt 3 : ℝ) ^ 5 = (-1 / Real.sqrt 3) * (-1 / Real.sqrt 3) ^ 4 := by ring 
            _ = (-1 / Real.sqrt 3) * (1 / 9) := by rw [h14]
            _ = -1 / (9 * Real.sqrt 3) := by 
              field_simp [h11']
              <;> nlinarith [Real.sqrt_nonneg 3, Real.sqrt_pos.2 (show (0 : ℝ) < 3 by norm_num)]
        simp only [h12, h13, h14, h15] 
        field_simp [h11']
        <;> nlinarith [Real.sqrt_nonneg 3, Real.sqrt_pos.2 (show (0 : ℝ) < 3 by norm_num)]