import Mathlib

open Real

theorem algebra_100909 (x : Fin 49 → ℝ) (h : ∑ i, (i + 1) * (x i)^2 = 1) :
    ∑ i, (i + 1) * x i ≤ 35 := by
  have h1 : (∑ i : Fin 49, (i + 1 : ℝ) * x i) ^ 2 ≤ 1225 := by
    have h2 : (∑ i : Fin 49, (i + 1 : ℝ) * x i) ^ 2 ≤ (∑ i : Fin 49, (i + 1 : ℝ) * (x i) ^ 2) * (∑ i : Fin 49, (i + 1 : ℝ)) := by
      have h3 : (∑ i : Fin 49, (i + 1 : ℝ) * x i) = (∑ i : Fin 49, (√(i + 1 : ℝ) * x i) * (√(i + 1 : ℝ))) := by
        apply Finset.sum_congr
        · rfl
        · intro i hi
          have h4 : (√(i + 1 : ℝ) * x i) * (√(i + 1 : ℝ)) = (i + 1 : ℝ) * x i := by
            calc
              (√(i + 1 : ℝ) * x i) * (√(i + 1 : ℝ)) = (√(i + 1 : ℝ)) * (√(i + 1 : ℝ)) * x i := by ring
              _ = ((√(i + 1 : ℝ)) ^ 2) * x i := by ring
              _ = (i + 1 : ℝ) * x i := by
                have h10 : (√(i + 1 : ℝ)) ^ 2 = (i + 1 : ℝ) := by
                  rw [Real.sq_sqrt]
                  have h11 : (i + 1 : ℝ) ≥ 0 := by
                    have h12 : (i : ℝ) ≥ 0 := by
                      simp at *
                    nlinarith
                  linarith
                rw [h10]
          linarith
      rw [h3]
      have h5 : (∑ i : Fin 49, (√(i + 1 : ℝ) * x i) * (√(i + 1 : ℝ))) ^ 2 ≤ (∑ i : Fin 49, (√(i + 1 : ℝ) * x i) ^ 2) * (∑ i : Fin 49, (√(i + 1 : ℝ)) ^ 2) := by
        apply Finset.sum_mul_sq_le_sq_mul_sq
      have h8 : ∑ i : Fin 49, (√(i + 1 : ℝ) * x i) ^ 2 = ∑ i : Fin 49, (i + 1 : ℝ) * (x i) ^ 2 := by
        apply Finset.sum_congr
        · rfl
        · intro i hi
          have h9 : (√(i + 1 : ℝ) * x i) ^ 2 = (i + 1 : ℝ) * (x i) ^ 2 := by
            calc
              (√(i + 1 : ℝ) * x i) ^ 2 = (√(i + 1 : ℝ) ^ 2) * (x i ^ 2) := by ring
              _ = (i + 1 : ℝ) * (x i ^ 2) := by
                have h10 : (√(i + 1 : ℝ)) ^ 2 = (i + 1 : ℝ) := by
                  rw [Real.sq_sqrt]
                  have h11 : (i + 1 : ℝ) ≥ 0 := by
                    have h12 : (i : ℝ) ≥ 0 := by
                      simp at *
                    nlinarith
                  linarith
                rw [h10]
          linarith
      have h11 : ∑ i : Fin 49, (√(i + 1 : ℝ)) ^ 2 = ∑ i : Fin 49, (i + 1 : ℝ) := by
        apply Finset.sum_congr
        · rfl
        · intro i hi
          have h12 : (√(i + 1 : ℝ)) ^ 2 = (i + 1 : ℝ) := by
            rw [Real.sq_sqrt]
            have h11 : (i + 1 : ℝ) ≥ 0 := by
              have h12 : (i : ℝ) ≥ 0 := by
                simp at *
              nlinarith
            linarith
          linarith
      rw [h8, h11] at h5
      linarith
    have h13 : (∑ i : Fin 49, (i + 1 : ℝ)) = 1225 := by
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
      all_goals norm_num
    have h14 : (∑ i : Fin 49, (i + 1 : ℝ) * (x i) ^ 2) = 1 := h
    rw [h13, h14] at h2
    linarith
  have h28 : ∑ i, (i + 1) * x i ≤ 35 := by
    nlinarith [sq_nonneg ((∑ i : Fin 49, (i + 1 : ℝ) * x i) - 35), Real.sqrt_nonneg (1225 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (1225 : ℝ) by norm_num)]
  simpa using h28