import Mathlib

theorem algebra_190837 (n : ℝ) (hn : n > 0) (h : n^2 + 3 * n - 28 = 0) :
    ∑ i ∈ Finset.range 30, (1 / (Real.sqrt (n + 2 * i) + Real.sqrt (n + 2 * i + 2))) = 3 := by
  have h1 : n = 4 := by
    nlinarith
  rw [h1]
  have h3 : ∀ i : ℕ, 1 / (Real.sqrt (4 + 2 * (i : ℝ)) + Real.sqrt (4 + 2 * (i : ℝ) + 2)) =
      (Real.sqrt (4 + 2 * (i : ℝ) + 2) - Real.sqrt (4 + 2 * (i : ℝ))) / 2 := by
    intro i
    have h4 : Real.sqrt (4 + 2 * (i : ℝ)) ≥ 0 := Real.sqrt_nonneg (4 + 2 * (i : ℝ))
    have h5 : Real.sqrt (4 + 2 * (i : ℝ) + 2) ≥ 0 := Real.sqrt_nonneg (4 + 2 * (i : ℝ) + 2)
    have h6 : Real.sqrt (4 + 2 * (i : ℝ)) ^ 2 = (4 + 2 * (i : ℝ) : ℝ) := by
      rw [Real.sq_sqrt]
      nlinarith
    have h7 : Real.sqrt (4 + 2 * (i : ℝ) + 2) ^ 2 = (4 + 2 * (i : ℝ) + 2 : ℝ) := by
      rw [Real.sq_sqrt]
      nlinarith
    field_simp [show Real.sqrt (4 + 2 * (i : ℝ)) + Real.sqrt (4 + 2 * (i : ℝ) + 2) ≠ 0 by positivity]
    <;> nlinarith [Real.sqrt_nonneg (4 + 2 * (i : ℝ)), Real.sqrt_nonneg (4 + 2 * (i : ℝ) + 2), Real.sq_sqrt (show (0 : ℝ) ≤ 4 + 2 * (i : ℝ) by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ (4 + 2 * (i : ℝ) + 2 : ℝ) by nlinarith)]
  have h4 : ∑ i in Finset.range 30, (1 / (Real.sqrt (4 + (2 * (i : ℝ))) + Real.sqrt (4 + 2 * (i : ℝ) + 2)) ) = ∑ i in Finset.range 30, ( (Real.sqrt (4 + 2 * (i : ℝ) + 2) - Real.sqrt (4 + 2 * (i : ℝ))) / 2 ) := by
    apply Finset.sum_congr
    · rfl
    · intro i hi
      specialize h3 i
      linarith
  have h7 : ∀ k : ℕ, ∑ i ∈ Finset.range k, ((Real.sqrt (4 + 2 * (i : ℝ) + 2) - Real.sqrt (4 + 2 * (i : ℝ))) / 2 ) = (Real.sqrt (4 + 2 * (k : ℝ)) - Real.sqrt (4 : ℝ)) / 2 := by
    intro k
    induction k with
    | zero =>
      simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      field_simp [Real.sqrt_nonneg (4 + 2 * (k : ℝ)), Real.sqrt_nonneg (4 + 2 * (k : ℝ) + 2)]
      <;> ring_nf 
  have h5 : Real.sqrt (4 : ℝ) = 2 := by
    rw [Real.sqrt_eq_cases]
    all_goals norm_num
  have h6 : ∑ i ∈ Finset.range 30, ((Real.sqrt (4 + 2 * (i : ℝ) + 2) - Real.sqrt (4 + 2 * (i : ℝ))) / 2 ) = (Real.sqrt (4 + 2 * (30 : ℝ)) - Real.sqrt (4 : ℝ)) / 2 := h7 30
  rw [h4, h6, h5]
  have h8 : Real.sqrt (4 + 2 * (30 : ℝ)) = 8 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  rw [h8]
  all_goals norm_num