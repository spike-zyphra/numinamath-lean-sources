import Mathlib

open Real

theorem inequalities_155625 {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) :
    (∑ i, x i) * (∑ i, 1 / x i) ≥ n ^ 2 := by 
  have h4 : (∑ i : Fin n, Real.sqrt (x i) * Real.sqrt (1 / x i)) ^ 2 ≤ (∑ i : Fin n, (Real.sqrt (x i) : ℝ) ^ 2) * (∑ i : Fin n, (Real.sqrt (1 / x i) : ℝ) ^ 2) := by 
    apply Finset.sum_mul_sq_le_sq_mul_sq
  have h5 : (∑ i : Fin n, Real.sqrt (x i) * Real.sqrt (1 / x i)) = (n : ℝ) := by
    have h6 : ∀ i : Fin n, Real.sqrt (x i) * Real.sqrt (1 / x i) = 1 := by 
      intro i
      have hx_pos : 0 < x i := hx i
      have hx_pos1 : 0 < 1 / x i := by
        apply div_pos
        norm_num
        all_goals linarith
      have h7 : Real.sqrt (x i) * Real.sqrt (1 / x i) = Real.sqrt ((x i) * (1 / x i)) := by
        rw [← Real.sqrt_mul (by positivity)]
      rw [h7]
      have : (x i) * (1 / x i) = 1 := by 
        field_simp [hx_pos.ne']
      rw [this]
      simp
    simp_rw [h6]
    simp [Finset.sum_const, Finset.card_univ, mul_add, add_mul]
    <;> ring
  have h8 : (∑ i : Fin n, (Real.sqrt (x i) : ℝ) ^ 2) = (∑ i : Fin n, x i) := by 
    apply Finset.sum_congr
    · rfl 
    · intro i hi 
      have hx_pos : 0 < x i := hx i
      have h9 : (Real.sqrt (x i) : ℝ) ^ 2 = x i := Real.sq_sqrt (by linarith)
      linarith 
  have h9 : (∑ i : Fin n, (Real.sqrt (1 / x i) : ℝ) ^ 2) = (∑ i : Fin n, 1 / x i) := by
    apply Finset.sum_congr
    · rfl 
    · intro i hi 
      have hx_pos : 0 < x i := hx i
      have hx_pos1 : 0 < 1 / x i := by 
        apply div_pos
        norm_num
        all_goals linarith
      have h10 : (Real.sqrt (1 / x i) : ℝ) ^ 2 = 1 / x i := Real.sq_sqrt (by positivity)
      linarith 
  rw [h5] at h4 
  rw [h8, h9] at h4 
  nlinarith