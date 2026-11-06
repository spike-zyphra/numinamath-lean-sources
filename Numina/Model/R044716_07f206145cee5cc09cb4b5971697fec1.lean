import Mathlib

theorem algebra_21057 : IsLeast {d : ℝ | ∃ C1 C2 : EuclideanSpace ℝ (Fin 2), (C1 0)^2 - 24 * (C1 0) + (C1 1)^2 - 32 * (C1 1) + 384 = 0 ∧ (C2 0)^2 + 24 * (C2 0) + (C2 1)^2 + 32 * (C2 1) + 384 = 0 ∧ d = dist C1 C2} 32 := by
  constructor
  · -- Show that 32 is in the set
    use ![48 / 5, 64 / 5], ![-48 / 5, -64 / 5]
    constructor
    · -- Verify first circle equation
      norm_num
      <;> nlinarith
    constructor
    · -- Verify second circle equation
      norm_num
      <;> nlinarith
    · -- Verify distance
      simp [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_succ, Fin.sum_univ_zero, Finset.sum]
      ring_nf
      have h1 : Real.sqrt 1024 = 32 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> nlinarith
      rw [h1]
      all_goals norm_num
  · -- Show that 32 is minimal
    intro d hd
    rcases hd with ⟨C1, C2, h1, h2, h3⟩
    have eq1 : (C1 0 - 12 : ℝ) ^ 2 + (C1 1 - 16 : ℝ) ^ 2 = 16 := by
      nlinarith
    have eq2 : (C2 0 + 12 : ℝ) ^ 2 + (C2 1 + 16 : ℝ) ^ 2 = 16 := by
      nlinarith
    have h4 : dist C1 C2 = Real.sqrt (∑ i : Fin 2, (C1 i - C2 i) ^ 2) := by
      simp [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_succ, Fin.sum_univ_zero, Finset.sum]
      <;> ring_nf
    have h5 : (∑ i : Fin 2, (C1 i - C2 i) ^ 2) ≥ 1024 := by
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at *
      nlinarith [sq_nonneg ((C1 0 - (C2 0)) - 96 / 5), sq_nonneg ((C1 1 - (C2 1)) - 128 / 5),
        sq_nonneg ((C1 0 - 12) - (C2 0 + 12)), sq_nonneg ((C1 1 - 16) - (C2 1 + 16)), 
        sq_nonneg ((C1 0 - 48 / 5) + (C2 0 + 48 / 5)), sq_nonneg ((C1 1 - 64 / 5) + (C2 1 + 64 / 5))]
    have h5' : Real.sqrt (∑ i : Fin 2, (C1 i - C2 i) ^ 2) ≥ 32 := by
      have h6 : Real.sqrt (∑ i : Fin 2, (C1 i - C2 i) ^ 2) ≥ Real.sqrt (1024 : ℝ) := Real.sqrt_le_sqrt (show (1024 : ℝ) ≤ ∑ i : Fin 2, (C1 i - C2 i) ^ 2 by linarith)
      have h6' : Real.sqrt (1024 : ℝ) = (32 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      linarith [h6, h6']
    linarith [h4, h5', h3]