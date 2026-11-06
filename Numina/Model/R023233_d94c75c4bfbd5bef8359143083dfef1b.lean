import Mathlib

theorem algebra_13008 {x : ℝ} (hx : x^2 - 2 * ⌊x⌋ - 2 = 0) :
    x = Real.sqrt 6 := by
  have h1 : (⌊x⌋ : ℝ) ≤ x := by 
    exact Int.floor_le x 
  have h2 : x < (⌊x⌋ + 1 : ℝ) := by 
    exact Int.lt_floor_add_one x
  have h3 : x^2 = 2 * (⌊x⌋ : ℝ) + 2 := by
    linarith
  have h4 : ⌊x⌋ ≥ 0 := by
    by_contra h
    push_neg at h
    have h6 : ⌊x⌋ ≤ -1 := by
      omega 
    have h7 : (⌊x⌋ : ℝ) ≤ (-1 : ℝ) := by
      exact_mod_cast h6
    nlinarith [h1, h2, h7, sq_nonneg (x + 1), sq_nonneg (x), h3]
  have h8 : ⌊x⌋ ≤ 2 := by
    by_contra h
    push_neg at h
    have h9 : ⌊x⌋ ≥ 3 := by
      omega 
    have h10 : (⌊x⌋ : ℝ) ≥ (3 : ℝ) := by
      exact_mod_cast h9
    nlinarith [h1, h2, h10, sq_nonneg (x - 3 : ℝ), sq_nonneg (x), h3, Real.sqrt_nonneg 6]
  have h11 : ⌊x⌋ = 0 ∨ ⌊x⌋ = 1 ∨ ⌊x⌋ = 2 := by
    omega
  rcases h11 with h11 | h11 | h11
  · -- case ⌊x⌋ = 0
    have h12 : (⌊x⌋ : ℝ) = 0 := by
      exact_mod_cast h11
    rw [h12] at h3
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  · -- case ⌊x⌋ = 1
    have h12 : (⌊x⌋ : ℝ) = 1 := by
      exact_mod_cast h11
    rw [h12] at h3
    nlinarith [Real.sqrt_nonneg (4 : ℝ)]
  · -- case ⌊x⌋ = 2
    have h12 : (⌊x⌋ : ℝ) = 2 := by
      exact_mod_cast h11
    rw [h12] at h3
    have hx2 : x ^ 2 = 6 := by
      linarith
    have h4 : x ≥ 2 := by
      nlinarith [Real.sqrt_nonneg (6 : ℝ), Real.sqrt_nonneg (6 : ℝ)]
    have h5 : x < 3 := by
      linarith [h2, h12]
    have hx6 : x = Real.sqrt 6 := by
      have h7 : x ^ 2 = 6 := hx2
      have h8 : x ≥ 0 := by nlinarith
      have h9 : x = Real.sqrt 6 := by
        rw [← h7]
        field_simp [h8]
      linarith
    exact_mod_cast hx6