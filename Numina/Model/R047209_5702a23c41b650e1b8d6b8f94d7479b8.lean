import Mathlib

theorem algebra_325086 :
    {x : ℝ | 0 ≤ x + 3 ∧ 0 ≤ 2 * x - 1 ∧ Real.sqrt (x + 3) + Real.sqrt (2 * x - 1) = 4} = {52 - 8 * Real.sqrt 39} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume x is in the left side, prove it's in the right
    rintro ⟨hx1, hx2, heq⟩
    have h1 : Real.sqrt (x + 3) ≥ 0 := by positivity
    have h2 : Real.sqrt (2 * x - 1) ≥ 0 := by positivity
    have h3 : Real.sqrt (x + 3) = -4 + Real.sqrt 39 := by
      nlinarith [Real.sqrt_nonneg (x + 3), Real.sqrt_nonneg (2 * x - 1), 
        Real.sq_sqrt (show 0 ≤ (x + 3 : ℝ) by linarith), 
        Real.sq_sqrt (show 0 ≤ (2 * x - 1 : ℝ) by linarith), 
        sq_nonneg (Real.sqrt (x + 3) - (-4 + Real.sqrt 39)), 
        sq_nonneg (Real.sqrt (2 * x - 1) - (8 - Real.sqrt 39)), 
        Real.sqrt_nonneg 39, Real.sq_sqrt (show (0 : ℝ) ≤ (39 : ℝ) by norm_num)
      ]
    have h4 : x = 52 - 8 * Real.sqrt 39 := by
      have h5 : Real.sqrt (x + 3) = -4 + Real.sqrt 39 := h3
      have h6 : (Real.sqrt (x + 3)) ^ 2 = x + 3 := by
        rw [Real.sq_sqrt]
        linarith
      rw [h5] at h6
      nlinarith [Real.sqrt_nonneg 39, Real.sq_sqrt (show (0 : ℝ) ≤ (39 : ℝ) by norm_num)]
    linarith
  · -- Assume x = 52 -8 * Real.sqrt 39, prove it's in the left side
    intro heq
    have h1 : x = 52 - 8 * Real.sqrt 39 := by
      linarith
    have hx1 : 0 ≤ x + 3 := by
      rw [h1]
      nlinarith [Real.sqrt_nonneg 39, Real.sq_sqrt (show (0 : ℝ) ≤ (39 : ℝ) by norm_num)]
    have hx2 : 0 ≤ 2 * x - 1 := by
      rw [h1]
      nlinarith [Real.sqrt_nonneg 39, Real.sq_sqrt (show (0 : ℝ) ≤ (39 : ℝ) by norm_num)]
    have heq : Real.sqrt (x + 3) + Real.sqrt (2 * x - 1) = 4 := by
      have h3 : Real.sqrt (x + 3) = -4 + Real.sqrt 39 := by
        have h5 : x = 52 - 8 * Real.sqrt 39 := by
          linarith
        rw [h5]
        have h6 : Real.sqrt ((52 - 8 * Real.sqrt 39 : ℝ) + 3) = -4 + Real.sqrt 39 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [Real.sqrt_nonneg 39, Real.sq_sqrt (show (0 : ℝ) ≤ (39 : ℝ) by norm_num)]
        linarith
      have h4 : Real.sqrt (2 * x - 1) = 8 - Real.sqrt 39 := by
        have h5 : x = 52 - 8 * Real.sqrt 39 := by
          linarith
        rw [h5]
        have h7 : Real.sqrt ((2 * (52 - 8 * Real.sqrt 39 : ℝ) - 1 : ℝ) ) = 8 - Real.sqrt 39 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [Real.sqrt_nonneg 39, Real.sq_sqrt (show (0 : ℝ) ≤ (39 : ℝ) by norm_num)]
        linarith
      rw [h3, h4]
      linarith
    exact ⟨hx1, hx2, heq⟩