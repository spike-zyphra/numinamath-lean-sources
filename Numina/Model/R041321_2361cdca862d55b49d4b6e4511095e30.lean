import Mathlib

theorem algebra_296339 {a b : ℚ} (h : a + b * √3 = √6 * √(1 + √(4 + 2 * √3))) : a + b = 4 := by
  have h1 : √(4 + 2 * √3) = √3 + 1 := by 
    have h2 : (√3 + 1 : ℝ) ^ 2 = 4 + 2 * √3 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    have h3 : √(4 + 2 * √3) = √3 + 1 := by
      have h4 : √(4 + 2 * √3) = Real.sqrt ((√3 + 1 : ℝ) ^ 2) := by
        rw [←h2]
        all_goals norm_num
      rw [h4]
      rw [Real.sqrt_sq (by positivity)]
      all_goals norm_num
    linarith [h3]

  have h2 : (1 + √(4 + 2 * √3) : ℝ) = 2 + √3 := by
    rw [h1]
    ring

  have h3 : √6 * √(1 + √(4 + 2 * √3)) = 3 + √3 := by
    rw [h2]
    -- Simplify $\sqrt{6} \cdot \sqrt{2 + \sqrt{3}}$ as $\sqrt{6 \cdot (2 + \sqrt{3})}$
    have h4 : Real.sqrt 6 * Real.sqrt (2 + Real.sqrt 3) = Real.sqrt (6 * (2 + Real.sqrt 3)) := by
      rw [← Real.sqrt_mul (by positivity)]
      all_goals norm_num
    have h5 : Real.sqrt (6 * (2 + Real.sqrt 3)) = 3 + Real.sqrt 3 := by
      have h6 : (3 + Real.sqrt 3 : ℝ) ^ 2 = 6 * (2 + Real.sqrt 3) := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      have h7 : Real.sqrt (6 * (2 + Real.sqrt 3)) = Real.sqrt ((3 + Real.sqrt 3) ^ 2) := by
        rw [←h6]
        all_goals ring_nf <;> norm_num
      rw [h7]
      rw [Real.sqrt_sq (by positivity)]
      all_goals norm_num
    rw [h4, h5]
    <;> ring_nf <;> norm_num
    <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]

  rw [h3] at h
  have h4 : (a : ℝ) = 3 := by
    have h5 : (a : ℝ) + (b : ℝ) * √3 = 3 + √3 := h
    have h6 : (a - 3 : ℝ) + (b - 1) * √3 = 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3]

    have h7 : (b - 1 : ℝ) = 0 := by
      by_contra h8
      have h8' : √3 = ((3 - (a : ℝ)) / (b - 1 : ℝ) : ℝ) := by
        have h9 : (a - 3 : ℝ) + (b - 1) * √3 = 0 := h6
        have h9' : (b - 1 : ℝ) * √3 = (3 - (a : ℝ) : ℝ) := by
          nlinarith
        have h10 : (b - 1 : ℝ) ≠ 0 := by
          intro h11
          apply h8
          linarith
        have h11 : √3 = ((3 - (a : ℝ) : ℝ) / (b - 1 : ℝ)) := by
          field_simp [h10] at h9' ⊢
          <;> nlinarith
        linarith [h11]

      have h10 : Irrational (√3) := by
        native_decide

      have h11 : ((3 - (a : ℝ) : ℝ) / (b - 1 : ℝ) : ℝ) = (↑((3 - a : ℚ)) / ((b - 1 : ℚ) : ℚ) : ℝ) := by
        simp
        all_goals norm_num
        <;> linarith

      rw [h8'] at h10
      -- Note that ((3 - a)/ (b - 1)) is rational since a, b ∈ ℚ
      -- This contradicts with irrationality of sqrt 3
      norm_cast at h10 ⊢
      <;> norm_cast at h11 ⊢
      <;> norm_num [Irrational] at h10 ⊢
      <;> norm_cast at h10 ⊢ <;> tauto

      all_goals norm_cast at h10 ⊢ <;> norm_cast at h8' ⊢

    have h8 : (a - 3 : ℝ) = 0 := by
      have h9 : (a - 3 : ℝ) + (b - 1 : ℝ) * √3 = 0 := h6
      rw [h7] at h9
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3]

    linarith

    all_goals nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3]

  have h4' : (b : ℝ) = 1 := by
    have h5 : (a : ℝ) + (b : ℝ) * √3 = 3 + √3 := h
    have h6 : (a - 3 : ℝ) + (b - 1) * √3 = 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3]

    have h7 : (b - 1 : ℝ) = 0 := by
      by_contra h8
      have h8' : √3 = ((3 - (a : ℝ)) / (b - 1 : ℝ) : ℝ) := by
        have h9 : (a - 3 : ℝ) + (b - 1 : ℝ) * √3 = 0 := h6
        have h9' : (b - 1 : ℝ) * √3 = (3 - (a : ℝ) : ℝ) := by
          nlinarith
        have h10 : (b - 1 : ℝ) ≠ 0 := by
          intro h11
          apply h8
          linarith
        have h11 : √3 = ((3 - (a : ℝ) : ℝ) / (b - 1 : ℝ)) := by
          field_simp [h10] at h9' ⊢
          <;> nlinarith
        linarith [h11]

      have h10 : Irrational (√3) := by
        native_decide

      have h11 : ((3 - (a : ℝ) : ℝ) / (b - 1 : ℝ) : ℝ) = (↑((3 - a : ℚ) ) / ↑( (b - 1 : ℚ) : ℚ) : ℝ) := by
        simp
        all_goals norm_num
        <;> linarith

      rw [h8'] at h10
      -- Note that ((3 - a)/ (b - 1)) is rational since a, b ∈ ℚ
      -- This contradicts with irrationality of sqrt 3
      norm_cast at h10 ⊢
      <;> norm_cast at h11 ⊢
      <;> norm_num [Irrational] at h10 ⊢
      <;> norm_cast at h10 ⊢ <;> tauto
      all_goals norm_cast at h10 ⊢ <;> norm_cast at h8' ⊢

    have h8 : (b : ℝ) = 1 := by
      nlinarith

    linarith
    all_goals nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3]

  have h8 : (a + b : ℝ) = 4 := by
    have ha : (a : ℝ) = 3 := h4
    have hb : (b : ℝ) = 1 := h4'
    nlinarith

  norm_cast at h8 ⊢
  <;> linarith
  <;> tauto