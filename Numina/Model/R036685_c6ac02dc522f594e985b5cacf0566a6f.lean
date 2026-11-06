import Mathlib

open Real

theorem inequalities_99945 (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) :
    ∃ x, 0 ≤ x ∧ x ≤ 1 ∧ ∑ i, abs (x - a i) ≥ n / 2 := by
  by_cases h : ∑ i : Fin n, a i ≥ (n / 2 : ℝ)
  · -- If the sum of a_i >= n/2, then x = 0 satisfies the condition.
    use 0
    constructor
    · -- Show 0 ≤ 0
      norm_num
    constructor
    · -- Show 0 ≤ 1
      norm_num
    have h2 : ∑ i : Fin n, abs (0 - a i) = ∑ i : Fin n, a i := by
      apply Finset.sum_congr
      · rfl
      · intro i hi
        simp [abs_of_nonpos (show (0 - a i : ℝ) ≤ 0 by linarith [ (ha i).1 ])]
        all_goals linarith [ (ha i).1 ]
    rw [h2]
    linarith [h]
  · -- If the sum of a_i < n/2, then x = 1 satisfies the condition.
    use 1
    constructor
    · -- Show 0 ≤ 1
      norm_num
    constructor
    · -- Show 1 ≤ 1
      norm_num
    have h3 : ∑ i : Fin n, abs (1 - a i) = ∑ i : Fin n, (1 - a i) := by
      apply Finset.sum_congr
      · rfl
      · intro i hi
        have h4 : a i ≤ 1 := (ha i).2
        have h5 : (1 - a i : ℝ) ≥ 0 := by linarith 
        rw [abs_of_nonneg h5]
        all_goals linarith
    rw [h3]
    have h4 : ∑ i : Fin n, (1 - a i) = (n : ℝ) - ∑ i : Fin n, a i := by 
      simp [Finset.sum_sub_distrib]
      <;> ring
    rw [h4]
    have h5 : (n : ℝ) - ∑ i : Fin n, a i ≥ (n / 2 : ℝ) := by
      linarith [h]
    linarith [h5]