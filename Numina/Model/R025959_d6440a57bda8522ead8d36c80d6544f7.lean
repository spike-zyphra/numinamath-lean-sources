import Mathlib

theorem inequalities_11915 (x : Fin 10 → ℝ) (h₁ : ∑ i, abs (x i - 1) ≤ 4) (h₂ : ∑ i, abs (x i - 2) ≤ 6) :
    (∑ i, x i) / 10 = 1.4 := by
  have h3 : abs (∑ i, (x i - 1)) ≤ ∑ i, abs (x i - 1) := by
    apply Finset.abs_sum_le_sum_abs
  have h4 : abs (∑ i, (x i - 1)) ≤ 4 := by
    linarith [h₁, h3]

  have h5 : abs (∑ i, (x i - 2)) ≤ ∑ i, abs (x i - 2) := by
    apply Finset.abs_sum_le_sum_abs

  have h6 : abs (∑ i, (x i - 2)) ≤ 6 := by
    linarith [h₂, h5]

  have h7 : -4 ≤ ∑ i, (x i - 1) := by
    cases' abs_le.mp h4 with h8 h9
    linarith

  have h8 : ∑ i, (x i - 1) ≤ 4 := by
    cases' abs_le.mp h4 with h8 h9
    linarith

  have h9 : -6 ≤ ∑ i, (x i - 2) := by
    cases' abs_le.mp h6 with h10 h11
    linarith

  have h10 : ∑ i, (x i - 2) ≤ 6 := by
    cases' abs_le.mp h6 with h10 h11
    linarith

  have eq1 : ∑ i, (x i - 1) = (∑ i, x i) - 10 := by
    simp [Finset.sum]
    <;> ring_nf

  have eq2 : ∑ i, (x i - 2) = (∑ i, x i) - 20 := by
    simp [Finset.sum]
    <;> ring_nf

  have h21 : ∑ i, x i = 14 := by
    linarith [h7, h8, h9, h10, eq1, eq2]

  have h22 : (∑ i, x i) / 10 = 1.4 := by
    rw [h21]
    norm_num

  exact h22