import Mathlib

theorem inequalities_151287 (x : Fin 10 → ℝ)
    (h₁ : ∑ i, |x i - 1| ≤ 4) (h₂ : ∑ i, |x i - 2| ≤ 6) :
    (∑ i, x i) / 10 = 1.4 := by
  have h3 : -4 ≤ (∑ i, (x i - 1 : ℝ)) ∧ (∑ i, (x i - 1 : ℝ)) ≤ 4 := by
    have h4 : ∑ i, |x i - 1| ≥ |∑ i, (x i - 1)| := by
      apply Finset.abs_sum_le_sum_abs
    have h5 : |∑ i, (x i - 1)| ≤ 4 := by
      linarith [h₁, h4]
    cases' abs_le.mp h5 with h6 h7
    constructor <;> linarith

  have h4 : -6 ≤ (∑ i, (x i - 2 : ℝ)) ∧ (∑ i, (x i - 2 : ℝ)) ≤ 6 := by
    have h5 : ∑ i, |x i - 2| ≥ |∑ i, (x i - 2)| := by
      apply Finset.abs_sum_le_sum_abs
    have h6 : |∑ i, (x i - 2)| ≤ 6 := by
      linarith [h₂, h5]
    cases' abs_le.mp h6 with h7 h8
    constructor <;> linarith

  have h5 : 6 ≤ (∑ i, (x i : ℝ)) ∧ (∑ i, (x i : ℝ)) ≤ 14 := by
    have h6 : (∑ i, (x i - 1 : ℝ)) = (∑ i, (x i : ℝ)) - 10 := by
      simp [Finset.sum]
      ring
    constructor
    · linarith [h3.1, h6]
    · linarith [h3.2, h6]

  have h6 : 14 ≤ (∑ i, (x i : ℝ)) ∧ (∑ i, (x i : ℝ)) ≤ 26 := by
    have h7 : (∑ i, (x i - 2 : ℝ)) = (∑ i, (x i : ℝ)) - 20 := by
      simp [Finset.sum]
      ring
    constructor
    · linarith [h4.1, h7]
    · linarith [h4.2, h7]

  have h7 : (∑ i, (x i : ℝ)) = 14 := by
    linarith [h5.1, h5.2, h6.1, h6.2]

  rw [h7]
  norm_num