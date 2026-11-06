import Mathlib

theorem algebra_15062 : Set.range (fun t : ℝ => (t ^ 2 + 3 / 4 * t) / (t ^ 2 + 1)) =
    Set.Icc (-1 / 8) (9 / 8) := by
  ext y
  simp only [Set.mem_range, Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · -- Assume y ∈ range of g
    rintro ⟨t, ht⟩
    have ht2 : t ^ 2 + 1 > 0 := by
      nlinarith [sq_nonneg t]
    have eq1 : (t ^ 2 + 3 / 4 * t) / (t ^ 2 + 1) = y := ht
    have eq2 : t ^ 2 + 3 / 4 * t = y * (t ^ 2 + 1) := by
      field_simp [ht2] at eq1 ⊢
      linarith
    have h1 : (y - 9 / 8) * (y + 1 / 8) ≤ 0 := by
      nlinarith [sq_nonneg (t * (y - 1) - 3 / 8), sq_nonneg (t - 4 / 3), sq_nonneg (t - 3), sq_nonneg (t + 1 / 3), sq_nonneg (y - 1), sq_nonneg (y - 1 / 8), sq_nonneg (t + 3 / 4), sq_nonneg (y - 9 / 8), sq_nonneg (y + 1 / 8), sq_nonneg ((t ^ 2) - 1), sq_nonneg (t * (y - 1))]
    constructor
    · -- Show that y ≥ -1/8
      nlinarith
    · -- Show that y ≤ 9/8
      nlinarith
  · -- Assume y ∈ [-1/8, 9/8]
    rintro ⟨hy1, hy2⟩
    by_cases h1 : y - 1 = 0
    · -- y = 1
      have hy_eq_1 : y = 1 := by linarith
      rw [hy_eq_1] at *
      use 4 / 3
      norm_num
    · -- y ≠ 1
      have h1' : y - 1 ≠ 0 := h1
      have h6 : ∃ t : ℝ, (y - 1) * t ^ 2 - 3 / 4 * t + y = 0 := by
        have h7 : (3 / 4 : ℝ) ^ 2 - 4 * (y - 1) * y ≥ 0 := by
          nlinarith
        use ( (3 / 4) + Real.sqrt ( (3 / 4) ^ 2 - 4 * (y - 1) * y ) ) / (2 * (y - 1) )
        field_simp [h1']
        ring_nf
        rw [Real.sq_sqrt (by nlinarith)]
        <;> nlinarith
      rcases h6 with ⟨t, ht⟩
      use t
      have ht2 : t ^ 2 + 1 > 0 := by
        nlinarith [sq_nonneg t]
      field_simp [ht2] at *
      nlinarith [ht]