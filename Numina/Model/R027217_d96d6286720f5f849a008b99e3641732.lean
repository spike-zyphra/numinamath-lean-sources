import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_99588 :
  IsLeast {x | ∃ t : Fin 5 → ℝ, (∀ i, 0 ≤ t i) ∧ (∑ i, t i) = 1 ∧ x = max (t 0 + t 1) (max (t 1 + t 2) (max (t 2 + t 3) (t 3 + t 4)))} (1 / 3) := by
  constructor
  · -- Show 1/3 is in the set
    use fun i => 
      match i with
      | 0 | 2 | 4 => (1 / 3 : ℝ)
      | 1 | 3 => (0 : ℝ)
      | _ => (0 : ℝ)
    constructor
    · intro i
      fin_cases i <;> norm_num 
    constructor
    · simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
      all_goals norm_num 
    · norm_num
      <;> simp [max_eq_left_of_lt, max_eq_right, le_refl]
      <;> norm_num 
  · -- Show 1/3 is minimal
    intro x hx
    rcases hx with ⟨t, ht_nonneg, ht_sum, hx⟩
    by_contra h
    push_neg at h
    have h1 : max (t 0 + t 1) (max (t 1 + t 2) (max (t 2 + t 3) (t 3 + t 4))) < (1 / 3 : ℝ) := by 
      linarith [h, hx]
    -- From the above assumption, each pair must be less than 1/3
    have h2 : t 0 + t 1 < (1 / 3 : ℝ) := by
      by_contra h2
      push_neg at h2
      have h3 : max (t 0 + t 1) (max (t 1 + t 2) (max (t 2 + t 3) (t 3 + t 4))) ≥ (t 0 + t 1 : ℝ) := by 
        simp [max_le_iff]
      linarith 
    have h3 : t 1 + t 2 < (1 / 3 : ℝ) := by
      by_contra h3
      push_neg at h3
      have h4 : max (t 0 + t 1) (max (t 1 + t 2) (max (t 2 + t 3) (t 3 + t 4))) ≥ (t 1 + t 2 : ℝ) := by 
        simp [max_le_iff]
      linarith 
    have h4 : t 2 + t 3 < (1 / 3 : ℝ) := by 
      by_contra h4
      push_neg at h4
      have h5 : max (t 0 + t 1) (max (t 1 + t 2) (max (t 2 + t 3) (t 3 + t 4))) ≥ (t 2 + t 3 : ℝ) := by 
        simp [max_le_iff]
      linarith 
    have h5 : t 3 + t 4 < (1 / 3 : ℝ) := by 
      by_contra h5
      push_neg at h5
      have h6 : max (t 0 + t 1) (max (t 1 + t 2) (max (t 2 + t 3) (t 3 + t 4))) ≥ (t 3 + t 4 : ℝ) := by 
        simp [max_le_iff]
      linarith 
    -- Now we derive a contradiction from these constraints
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at ht_sum ⊢
    linarith [ht_sum, ht_nonneg 0, ht_nonneg 1, ht_nonneg 2, ht_nonneg 3, ht_nonneg 4]