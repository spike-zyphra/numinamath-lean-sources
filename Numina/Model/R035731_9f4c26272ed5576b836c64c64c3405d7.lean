import Mathlib

theorem inequalities_297785 (x : Fin 10 → ℝ) (h₁ : ∑ i, abs (x i - 1) ≤ 4)
    (h₂ : ∑ i, abs (x i - 2) ≤ 6) :
    (∑ i, x i) / 10 = 1.4 := by
  have h3 : ∑ i, (x i - 1) ≤ ∑ i, abs (x i - 1) := by
    apply Finset.sum_le_sum
    intro i hi
    cases abs_cases (x i - 1) with
    | inl h => 
      linarith
    | inr h => 
      linarith
  have h4 : ∑ i, (x i - 1) ≤ 4 := by 
    linarith [h₁, h3]
  have h5 : ∑ i, x i ≤ 14 := by
    have eq : ∑ i, (x i - 1) = (∑ i, x i) - 10 := by
      simp [Finset.sum]
      <;> ring
    linarith [eq, h4]

  have h6 : ∑ i, (2 - x i) ≤ ∑ i, abs (x i - 2) := by 
    apply Finset.sum_le_sum
    intro i hi
    cases abs_cases (x i - 2) with
    | inl h => 
      linarith
    | inr h => 
      linarith

  have h7 : ∑ i, (2 - x i) ≤ 6 := by
    linarith [h₂, h6]

  have eq1 : ∑ i, (2 - x i) = 20 - (∑ i, x i) := by 
    simp [Finset.sum]
    <;> ring

  have h8 : 20 - (∑ i, x i) ≤ 6 := by
    linarith [eq1, h7]

  have h9 : ∑ i, x i ≥ 14 := by
    linarith [h8]

  have h10 : ∑ i, x i = 14 := by
    linarith [h9, h5]

  have h11 : (∑ i, x i) / 10 = 1.4 := by 
    rw [h10]
    all_goals norm_num

  exact h11