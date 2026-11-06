import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_10608 :
  IsLeast {M | ∃ x : Fin 5 → ℝ,
    (∀ i, 0 ≤ x i) ∧ (∑ i, x i) = 300 ∧
    M = max (max (max (x 0 + x 1) (x 1 + x 2)) (x 2 + x 3)) (x 3 + x 4)} 100 := by
  constructor
  · -- First part: prove that 100 is achievable
    use λ i =>
      match i with
      | 0 | 2 | 4 => 100
      | 1 | 3 => 0
      | _ => 0
    constructor
    · intro i
      fin_cases i <;> norm_num
    constructor
    · simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
      all_goals norm_num
    · norm_num
  · -- Show that no value less than 100 is achievable
    intro M h
    rcases h with ⟨x, hx, hsum, hM⟩
    have h1 : 0 ≤ x 0 := hx 0
    have h2 : 0 ≤ x 1 := hx 1
    have h3 : 0 ≤ x 2 := hx 2
    have h4 : 0 ≤ x 3 := hx 3
    have h5 : 0 ≤ x 4 := hx 4
    have eq1 : x 0 + x 1 + x 2 + x 3 + x 4 = 300 := by
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at hsum ⊢
      linarith
    by_contra h
    push_neg at h
    have h6 : x 0 + x 1 < (100 : ℝ) := by
      by_contra h7
      push_neg at h7
      have h7' : max (max (max (x 0 + x 1) (x 1 + x 2)) (x 2 + x 3)) (x 3 + x 4) ≥ (100 : ℝ) := by
        have h8 : x 0 + x 1 ≥ (100 : ℝ) := by linarith
        have h9 : max (max (max (x 0 + x 1) (x 1 + x 2)) (x 2 + x 3)) (x 3 + x 4) ≥ x 0 + x 1 := by
          simp
        linarith
      linarith [show max (max (max (x 0 + x 1) (x 1 + x 2)) (x 2 + x 3)) (x 3 + x 4) = M by linarith [hM], h, h7']
    have h7 : x 1 + x 2 < (100 : ℝ) := by
      by_contra h8
      push_neg at h8
      have h8' : max (max (max (x 0 + x 1) (x 1 + x 2)) (x 2 + x 3)) (x 3 + x 4) ≥ (100 : ℝ) := by
        have h9 : x 1 + x 2 ≥ (100 : ℝ) := by linarith
        have h10 : max (max (max (x 0 + x 1) (x 1 + x 2)) (x 2 + x 3)) (x 3 + x 4) ≥ x 1 + x 2 := by
          simp
        linarith
      linarith [show max (max (max (x 0 + x 1) (x 1 + x 2)) (x 2 + x 3)) (x 3 + x 4) = M by linarith [hM], h, h8']
    have h8 : x 2 + x 3 < (100 : ℝ) := by
      by_contra h9
      push_neg at h9
      have h9' : max (max (max (x 0 + x 1) (x 1 + x 2)) (x 2 + x 3)) (x 3 + x 4) ≥ (100 : ℝ) := by
        have h10 : x 2 + x 3 ≥ (100 : ℝ) := by linarith
        have h11 : max (max (max (x 0 + x 1) (x 1 + x 2)) (x 2 + x 3)) (x 3 + x 4) ≥ x 2 + x 3 := by
          simp
        linarith
      linarith [show max (max (max (x 0 + x 1) (x 1 + x 2)) (x 2 + x 3)) (x 3 + x 4) = M by linarith [hM], h, h9']
    have h9 : x 3 + x 4 < (100 : ℝ) := by
      by_contra h10
      push_neg at h10
      have h10' : max (max (max (x 0 + x 1) (x 1 + x 2)) (x 2 + x 3)) (x 3 + x 4) ≥ (100 : ℝ) := by
        have h11 : x 3 + x 4 ≥ (100 : ℝ) := by linarith
        have h12 : max (max (max (x 0 + x 1) (x 1 + x 2)) (x 2 + x 3)) (x 3 + x 4) ≥ x 3 + x 4 := by
          simp
        linarith
      linarith [show max (max (max (x 0 + x 1) (x 1 + x 2)) (x 2 + x 3)) (x 3 + x 4) = M by linarith [hM], h, h10']
    nlinarith [sq_nonneg (x 0 - 100 : ℝ), sq_nonneg (x 1 : ℝ), sq_nonneg (x 2 - 100 : ℝ), sq_nonneg (x 3 : ℝ), sq_nonneg (x 4 - 100 : ℝ), 
      h6, h7, h8, h9, 
        mul_nonneg (show (0 : ℝ) ≤ x 0 by linarith) (show (0 : ℝ) ≤ x 1 by linarith), 
          mul_nonneg (show (0 : ℝ) ≤ x 1 by linarith) (show (0 : ℝ) ≤ x 2 by linarith), 
            mul_nonneg (show (0 : ℝ) ≤ x 2 by linarith) (show (0 : ℝ) ≤ x 3 by linarith), 
              mul_nonneg (show (0 : ℝ) ≤ x 3 by linarith) (show (0 : ℝ) ≤ x 4 by linarith)
              ]