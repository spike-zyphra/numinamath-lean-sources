import Mathlib

open Real

theorem inequalities_152450 (n : ℕ) (x a : Fin n → ℝ)
    (h : ∑ i, (x i)^2 = 1) :
    ∑ i, a i * x i ≤ sqrt (∑ i, (a i)^2) := by
  have h1 : (∑ i, a i * x i) ^ 2 ≤ (∑ i, (a i)^2) * (∑ i, (x i)^2) := by
    apply Finset.sum_mul_sq_le_sq_mul_sq
  have h2 : (∑ i, (x i)^2) = 1 := h
  have h3 : (∑ i, a i * x i) ^ 2 ≤ (∑ i, (a i)^2) := by
    rw [h2] at h1
    linarith
  have h4 : (∑ i, a i * x i) ≤ Real.sqrt ((∑ i, (a i)^2)) := by
    have h5 : (∑ i, a i * x i) ≤ Real.sqrt ((∑ i, (a i)^2) * (∑ i, (x i)^2)) := by
      have h6 : (∑ i, a i * x i) ≤ |(∑ i, a i * x i)| := by
        apply le_abs_self
      have h7 : |(∑ i, a i * x i)| ≤ Real.sqrt ((∑ i, (a i)^2) * (∑ i, (x i)^2)) := by
        have h8 : |(∑ i, a i * x i)| = Real.sqrt ((∑ i, a i * x i) ^ 2) := by
          rw [Real.sqrt_sq_eq_abs]
        have h9 : Real.sqrt ((∑ i, a i * x i) ^ 2) ≤ Real.sqrt ((∑ i, (a i)^2) * (∑ i, (x i)^2)) := by
          apply Real.sqrt_le_sqrt
          linarith [h1]
        linarith [h8, h9]
      linarith [h6, h7]
    have h6 : (∑ i, (a i)^2) * (∑ i, (x i)^2) = (∑ i, (a i)^2) := by
      rw [h]
      all_goals ring
    have h7 : Real.sqrt ((∑ i, (a i)^2) * (∑ i, (x i)^2)) = Real.sqrt ((∑ i, (a i)^2)) := by
      rw [h6]
    rw [h7] at h5
    linarith
  exact h4