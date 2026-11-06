import Mathlib

theorem algebra_93445 (S : Finset ℝ) (hS : S.card = 50) (hS1 : ∑ x ∈ S, x = 38 * 50)
    (hS2 : 45 ∈ S) (hS3 : 55 ∈ S) :
    (S \ {45, 55}).card = 48 ∧ ∑ x ∈ (S \ {45, 55}), x = 37.5 * 48 := by

  have h1 : (S \ {45, 55}).card = 48 := by
    have h45 : (45 : ℝ) ∈ S := hS2
    have h55 : (55 : ℝ) ∈ S := hS3
    have h45_55 : (45 : ℝ) ≠ (55 : ℝ) := by norm_num
    have h2 : (S \ {45, 55}).card = S.card - ({45, 55} : Finset ℝ).card := by
      rw [Finset.card_sdiff (show {45, 55} ⊆ S by 
        intro x hx
        simp at hx
        rcases hx with (rfl | rfl)
        · exact hS2
        · exact hS3
      )]
    have h3 : ({45, 55} : Finset ℝ).card = 2 := by
      rw [Finset.card_pair]
      norm_num
    rw [h3] at h2
    rw [hS] at h2
    norm_num at h2 ⊢
    all_goals
      linarith 
  constructor
  · exact h1

  · -- Compute the sum of the remaining elements
    have h2 : ∑ x in (S \ {45, 55}), x = (∑ x in S, x) - ∑ x in ({45, 55} : Finset ℝ), x := by
      rw [← Finset.sum_sdiff (show {45, 55} ⊆ S by 
        intro x hx
        simp at hx
        rcases hx with (rfl | rfl)
        · exact hS2
        · exact hS3
      )]
      all_goals 
        try simp 
    rw [h2]
    have h3 : ∑ x in ({45, 55} : Finset ℝ), x = (45 + 55 : ℝ) := by 
      norm_num [Finset.sum_insert, Finset.sum_singleton]
    rw [h3]
    rw [hS1]
    all_goals 
      norm_num