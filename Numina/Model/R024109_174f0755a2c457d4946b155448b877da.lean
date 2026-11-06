import Mathlib

open Real

theorem inequalities_146844 {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) :
    (∑ i, x i) * (∑ i, 1 / x i) ≥ n ^ 2 := by
  have h2 : (∑ i : Fin n, x i) * (∑ i : Fin n, 1 / x i) ≥ (n : ℝ) ^ 2 := by
    have h3 : (∑ i : Fin n, (Real.sqrt (x i) : ℝ) * (Real.sqrt (1 / x i) : ℝ)) = (n : ℝ) := by
      have h4 : ∀ i : Fin n, (Real.sqrt (x i) : ℝ) * (Real.sqrt (1 / x i) : ℝ) = 1 := by
        intro i
        have hx_i_pos : x i > 0 := hx i
        have h5 : Real.sqrt (1 / x i) = 1 / Real.sqrt (x i) := by
          field_simp [Real.sqrt_pos.2 hx_i_pos]
        rw [h5]
        field_simp [Real.sqrt_pos.2 hx_i_pos]
      have h4' : (∑ i : Fin n, (Real.sqrt (x i) : ℝ) * (Real.sqrt (1 / x i) : ℝ)) = ∑ i : Fin n, (1 : ℝ) := by
        congr
        funext i
        specialize h4 i
        simpa using h4
      rw [h4']
      simp
    have h6 : (∑ i : Fin n, (Real.sqrt (x i) : ℝ) * (Real.sqrt (1 / x i) : ℝ)) ^ 2 ≤ (∑ i : Fin n, (Real.sqrt (x i) : ℝ) ^ 2) * (∑ i : Fin n, (Real.sqrt (1 / x i) : ℝ) ^ 2) := by
      apply Finset.sum_mul_sq_le_sq_mul_sq
    have h7 : (∑ i : Fin n, (Real.sqrt (x i) : ℝ) ^ 2) = (∑ i : Fin n, x i) := by
      apply Finset.sum_congr
      · rfl
      · intro i hi
        have h11 : 0 ≤ x i := by
          linarith [hx i]
        rw [Real.sq_sqrt]
        all_goals linarith
    have h8 : (∑ i : Fin n, (Real.sqrt (1 / x i) : ℝ) ^ 2) = (∑ i : Fin n, 1 / x i) := by
      apply Finset.sum_congr
      · rfl
      · intro i hi
        have hx_i_pos : x i > 0 := hx i
        have hx1_nonneg : 0 ≤ (1 / x i : ℝ) := by
          have hx2_pos : 0 < (1 / x i : ℝ) := by
            apply one_div_pos.mpr
            exact hx_i_pos
          linarith
        rw [Real.sq_sqrt]
        all_goals
          exact hx1_nonneg
    rw [h3] at h6
    rw [h7, h8] at h6
    linarith
  linarith [h2]