import Mathlib

theorem algebra_126836 :
    IsGreatest {x : ℝ | ∃ a : Fin 6 → ℝ, x = a 5 ∧
      (∀ i j, i < j → a i ≤ a j) ∧
      ∑ i, a i = 10 ∧ ∑ i, (a i - 1)^2 = 6} (3 + 1 / 3) := by
  simp only [IsGreatest, Set.mem_setOf_eq, upperBounds, exists_and_right,
    exists_eq_right, and_imp]
  constructor
  · -- Show that 3 + 1/3 is in the set.
    have h1: (3 + 1 / 3 : ℝ) ∈ {x : ℝ | ∃ a : Fin 6 → ℝ, x = a 5 ∧
        (∀ i j, i < j → a i ≤ a j) ∧
        ∑ i, a i = 10 ∧ ∑ i, (a i - 1)^2 = 6} := by 
      use λ i =>
        match i with
        | 5 => 10 / 3
        | 0 | 1 | 2 | 3 | 4 => 4 / 3
        | _ => (0 : ℝ)
      constructor
      · -- x = a 5
        have h11: (3 + 1/3 : ℝ) = (10 / 3 : ℝ) := by
          norm_num 
        have h17: (3 + 1/3 : ℝ) = (10 / 3 : ℝ) := h11
        have h18: (10 / 3 : ℝ) = (10 / 3 : ℝ) := by 
          rfl 
        exact_mod_cast h11
      constructor
      · -- Show that `a` is non-decreasing.
        intro i j h
        fin_cases i <;> fin_cases j <;> simp at *
        all_goals norm_num
      constructor
      · -- Show that the sum is 10.
        simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
        norm_num
      · -- Show that the squared sum is 6.
        simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
        norm_num
    exact h1
  · -- Show that 3 + 1/3 is greatest.
    intro x hx
    rcases hx with ⟨a, hx1, ha1, ha2, ha3⟩
    have h1: x = a 5 := hx1
    have h2: a 0 ≤ a 1 := ha1 0 1 (by simp)
    have h3: a 1 ≤ a 2 := ha1 1 2 (by simp)
    have h4: a 2 ≤ a 3 := ha1 2 3 (by simp)
    have h5: a 3 ≤ a 4 := ha1 3 4 (by simp)
    have h6: a 4 ≤ a 5 := ha1 4 5 (by simp)
    have h7: a 0 + a 1 + a 2 + a 3 + a 4 + a 5 = 10 := by
      have hsum := ha2
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at hsum ⊢
      linarith
    have h8: (a 0 - 1: ℝ)^2 + (a 1 - 1)^2 + (a 2 - 1)^2 + (a 3 - 1)^2 + (a 4 - 1)^2 + (a 5 - 1)^2 = 6 := by
      have hsum := ha3
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at hsum ⊢
      linarith
    have h9: x = a 5 := h1
    nlinarith [sq_nonneg (a 0 - 4 / 3), sq_nonneg (a 1 - 4 / 3), sq_nonneg (a 2 - 4 / 3), sq_nonneg (a 3 - 4 / 3), sq_nonneg (a 4 - 4 / 3), sq_nonneg (a 5 - 10 / 3),
      sq_nonneg (a 0 - a 1), sq_nonneg (a 1 - a 2), sq_nonneg (a 2 - a 3), sq_nonneg (a 3 - a 4), sq_nonneg (a 4 - a 5)
    ]