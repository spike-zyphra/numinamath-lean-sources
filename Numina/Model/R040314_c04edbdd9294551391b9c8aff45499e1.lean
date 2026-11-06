import Mathlib

open Real

theorem algebra_320571 (x : ℝ) (hx : x > 0) :
    sqrt x + 1 / sqrt x - sqrt (x + 1 / x + 1) ≤ 2 - sqrt 3 ∧
    ∃ x : ℝ, x > 0 ∧ sqrt x + 1 / sqrt x - sqrt (x + 1 / x + 1) = 2 - sqrt 3 := by

  have h1 : sqrt x + 1 / sqrt x - sqrt (x + 1 / x + 1) ≤ 2 - sqrt 3 := by
    have ht1 : sqrt x > 0 := by apply Real.sqrt_pos.mpr hx
    have ht2 : sqrt x + 1 / sqrt x ≥ 2 := by
      have h3 : sqrt x * (1 / sqrt x) = 1 := by
        field_simp [ht1]
      have h4 : sqrt x + 1 / sqrt x - 2 ≥ 0 := by
        have h5 : sqrt x + 1 / sqrt x - 2 = (sqrt x ^ 2 + 1 - 2 * sqrt x) / sqrt x := by
          field_simp [ht1]
          <;> ring_nf <;> field_simp [ht1]
          <;> nlinarith [Real.sqrt_pos.mpr hx]
        rw [h5]
        have h6 : sqrt x ^ 2 + 1 - 2 * sqrt x ≥ 0 := by
          nlinarith [sq_nonneg (sqrt x - 1)]
        apply div_nonneg h6 (by positivity)
      linarith
    have h2 : x + 1 / x = (sqrt x + 1 / sqrt x) ^ 2 - 2 := by
      field_simp [ht1]
      <;> nlinarith [Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith), Real.sqrt_nonneg x]
    have h3 : (x + 1 / x + 1 : ℝ) = (sqrt x + 1 / sqrt x) ^ 2 - 1 := by
      linarith [h2]
    -- Now, sqrt (x + 1 / x + 1) = sqrt ((sqrt x + 1 / sqrt x ) ^ 2 - 1)
    have h5 : sqrt x + 1 / sqrt x - sqrt (x + 1 / x + 1) ≤ 2 - sqrt 3 := by
      have eq1 : sqrt (x + 1 / x + 1) = Real.sqrt ((sqrt x + 1 / sqrt x) ^ 2 - 1) := by
        rw [h3]
        <;> ring_nf
      have h51 : sqrt x + 1 / sqrt x - sqrt (x + 1 / x + 1) = (sqrt x + 1 / sqrt x) - Real.sqrt ((sqrt x + 1 / sqrt x) ^ 2 - 1) := by
        rw [eq1]
        <;> ring_nf
      rw [h51]
      have ht3 : sqrt x + 1 / sqrt x ≥ 2 := ht2
      have h6 : ((sqrt x + 1 / sqrt x) : ℝ) ≥ (2 : ℝ) := by linarith
      have h7 : (sqrt x + 1 / sqrt x - (2 - sqrt 3)) ≤ Real.sqrt ((sqrt x + 1 / sqrt x) ^ 2 - 1) := by
        have h11 : (sqrt x + 1 / sqrt x - (2 - sqrt 3)) ≥ 0 := by
          nlinarith [ht2, Real.sqrt_pos.mpr hx, Real.sq_sqrt (show (0 : ℝ) ≤ (3: ℝ) by norm_num), Real.sqrt_nonneg (3 : ℝ)]
        have h12 : Real.sqrt ((sqrt x + 1 / sqrt x) ^ 2 - 1) ≥ 0 := Real.sqrt_nonneg ((sqrt x + 1 / sqrt x) ^ 2 - 1)
        have h7 : (sqrt x + 1 / sqrt x - (2 - sqrt 3)) ^ 2 ≤ (Real.sqrt ((sqrt x + 1 / sqrt x) ^ 2 - 1)) ^ 2 := by
          have h8 : (Real.sqrt ((sqrt x + 1 / sqrt x) ^ 2 - 1)) ^ 2 = (sqrt x + 1 / sqrt x) ^ 2 - 1 := by
            apply Real.sq_sqrt
            nlinarith [sq_nonneg (sqrt x - 1 / sqrt x), Real.sqrt_pos.mpr hx, ht2]
          nlinarith [sq_nonneg ((sqrt x + 1 / sqrt x) - 2), sq_nonneg (Real.sqrt ((sqrt x + 1 / sqrt x) ^ 2 - 1) - sqrt 3),
            Real.sqrt_nonneg ((sqrt x + 1 / sqrt x) ^ 2 - 1),
            Real.sqrt_nonneg (3: ℝ),
            sq_nonneg (sqrt x + 1 / sqrt x - 2), Real.sq_sqrt (show (0 : ℝ) ≤ (3: ℝ) by norm_num),
            Real.sq_sqrt (show (0 : ℝ) ≤ ((sqrt x + 1 / sqrt x) ^ 2 - 1: ℝ) by nlinarith [sq_nonneg (sqrt x - 1 / sqrt x), Real.sqrt_pos.mpr hx, ht2]), sq_nonneg ((sqrt x + 1 / sqrt x) * (sqrt x + 1 / sqrt x) - 4)]
          <;> ring_nf
          all_goals nlinarith [ht2, Real.sqrt_nonneg ((sqrt x + 1 / sqrt x) ^ 2 - 1), Real.sqrt_nonneg (3 : ℝ)]
        nlinarith [Real.sqrt_nonneg ((sqrt x + 1 / sqrt x) ^ 2 - 1), Real.sq_sqrt (show (0 : ℝ) ≤ (3: ℝ) by norm_num), Real.sqrt_nonneg (3: ℝ)]
      linarith
    linarith

  have h_eq : ∃ x : ℝ, x > 0 ∧ sqrt x + 1 / sqrt x - sqrt (x + 1 / x + 1) = 2 - sqrt 3 := by
    use 1
    constructor
    · -- Show that 1 > 0
      norm_num
    · -- Show that at x = 1, the expression equals 2 - sqrt 3
      have h1 : sqrt (1 : ℝ) = 1 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h1]
      field_simp
      <;> ring_nf <;> norm_num [Real.sq_sqrt, Real.sqrt_nonneg]
      all_goals nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  constructor
  · -- Show that the expression ≤ 2 - sqrt 3 for all x > 0
    exact h1
  · -- Show that there exists x > 0 such that the expression = 2 - sqrt 3
    exact h_eq