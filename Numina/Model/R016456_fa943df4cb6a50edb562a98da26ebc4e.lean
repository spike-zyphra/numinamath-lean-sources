import Mathlib

open Real Set

theorem inequalities_190729 (a b : Fin 5 → ℝ)
    (ha : ∀ i, 5 ≤ a i ∧ a i ≤ 10) (hb : ∀ i, 5 ≤ b i ∧ b i ≤ 10) :
    2 * ∑ i, a i * b i ≤ ∑ i, (a i)^2 + ∑ i, (b i)^2 ∧
    ∑ i, (a i)^2 + ∑ i, (b i)^2 ≤ 5 / 2 * ∑ i, a i * b i := by
  constructor
  · -- Prove the first inequality
    have h1 : ∑ i, (a i - b i) ^ 2 ≥ 0 := by
      apply Finset.sum_nonneg
      intro i hi
      apply sq_nonneg
    have h2 : ∑ i, (a i - b i) ^ 2 = ∑ i, (a i)^2 + ∑ i, (b i)^2 - 2 * ∑ i, a i * b i := by
      simp [Finset.sum, sub_sq]
      <;> ring
    linarith
  · -- Prove the second inequality
    have h3 : ∀ i, a i ^ 2 + b i ^ 2 ≤ (5 / 2) * (a i * b i) := by
      intro i
      have h4 : 2 * (a i)^2 + 2 * (b i)^2 - 5 * (a i * b i) ≤ 0 := by
        have h6 : 2 * (a i)^2 + 2 * (b i)^2 - 5 * (a i * b i) = (2 * (a i) - (b i)) * ((a i) - 2 * (b i)) := by
          ring_nf
        rw [h6]
        have ha1 : 5 ≤ a i := (ha i).1
        have ha2 : a i ≤ 10 := (ha i).2
        have hb1 : 5 ≤ b i := (hb i).1
        have hb2 : b i ≤ 10 := (hb i).2
        have h8 : (2 * (a i) - (b i)) ≥ 0 := by nlinarith
        have h9 : ((a i) - 2 * (b i)) ≤ 0 := by nlinarith
        nlinarith [mul_nonpos_of_nonneg_of_nonpos h8 h9]
      linarith
    have h5 : ∑ i, (a i ^ 2 + b i ^ 2) ≤ 5 / 2 * ∑ i, a i * b i := by
      have h6 : ∀ i, a i ^ 2 + b i ^ 2 ≤ (5 / 2) * (a i * b i) := h3
      have h7 : ∑ i, (a i ^ 2 + b i ^ 2) ≤ ∑ i, ((5 / 2) * (a i * b i)) := by
        apply Finset.sum_le_sum
        intro i hi
        exact h6 i
      have h8 : ∑ i, ((5 / 2) * (a i * b i)) = (5 / 2) * ∑ i, (a i * b i) := by
        simp [Finset.mul_sum]
        <;> ring
      linarith [h7, h8]
    have h9 : ∑ i, (a i ^ 2 + b i ^ 2) = ∑ i, (a i) ^ 2 + ∑ i, (b i) ^ 2 := by
      simp [Finset.sum]
      <;> ring
    linarith [h9, h5]