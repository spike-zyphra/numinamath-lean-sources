import Mathlib

open Finset Real

theorem inequalities_224566 (n : ℕ) (hn : 0 < n) (x : ℕ → ℝ)
    (hx : ∀ i ∈ Icc 1 n, 0 < x i) :
    (∑ i ∈ Icc 1 n, x i) * (∑ i ∈ Icc 1 n, 1 / x i) ≥ n ^ 2 := by
  have h3 : ∀ i ∈ Icc 1 n, x i > 0 := by
    intro i hi
    specialize hx i hi
    linarith
  have h4 : (∑ i in Icc 1 n, (Real.sqrt (x i) * Real.sqrt (1 / x i))) ^ 2 ≤
    (∑ i in Icc 1 n, (Real.sqrt (x i) ^ 2)) * (∑ i in Icc 1 n, (Real.sqrt (1 / x i) ^ 2)) := by 
    apply Finset.sum_mul_sq_le_sq_mul_sq
  have h5 : ∑ i in Icc 1 n, (Real.sqrt (x i) * Real.sqrt (1 / x i)) = n := by 
    have h3' : ∀ i ∈ Icc 1 n, 0 < x i := by
      intro i hi
      apply h3 i hi
    have h4' : ∀ i ∈ Icc 1 n, Real.sqrt (x i) * Real.sqrt (1 / x i) = 1 := by
      intro i hi
      have hx' : x i > 0 := h3' i hi
      have h4 : Real.sqrt (x i) * Real.sqrt (1 / x i) = 1 := by 
        have h5 : Real.sqrt (x i) * Real.sqrt (1 / x i) = Real.sqrt (x i * (1 / x i)) := by 
          rw [Real.sqrt_mul]
          all_goals
            positivity
        rw [h5]
        have h6 : x i * (1 / x i) = 1 := by
          field_simp [hx']
        rw [h6]
        all_goals norm_num
      exact h4
    rw [sum_congr rfl (fun i hi => h4' i hi)]
    simp [h3']
    <;> try { tauto }
  have h6 : (∑ i in Icc 1 n, (Real.sqrt (x i) ^ 2)) = ∑ i in Icc 1 n, x i := by
    apply sum_congr
    · rfl
    · intro i hi
      have hx' : x i > 0 := h3 i hi
      have h8 : Real.sqrt (x i) ^ 2 = x i := by
        exact Real.sq_sqrt (by linarith)
      linarith [h8]
  have h7 : (∑ i in Icc 1 n, (Real.sqrt (1 / x i) ^ 2)) = ∑ i in Icc 1 n, 1 / x i := by
    apply sum_congr
    · rfl
    · intro i hi
      have hx' : x i > 0 := h3 i hi
      have h8 : Real.sqrt (1 / x i) ^ 2 = 1 / x i := by
        exact Real.sq_sqrt (by positivity)
      linarith [h8]
  rw [h5] at h4
  rw [h6, h7] at h4
  nlinarith [h4]