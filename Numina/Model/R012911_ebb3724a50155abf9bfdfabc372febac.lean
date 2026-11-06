import Mathlib


theorem number_theory_718 (S : Finset ℕ) (hS : S.card = 8) (hS1 : ∀ s ∈ S, Nat.Prime s)
    (hS2 : ∀ s ∈ S, s ≤ 20) (hS3 : ∑ s ∈ S, s^2 = 4 * ∏ s ∈ S, s - 36294) :
    S = {2, 2, 2, 2, 11, 13, 13, 13} := by
  have h4 : S ⊆ (Finset.Iic 20) := by
    intro x hx
    have h5 : x ≤ 20 := hS2 x hx
    simp at *
    all_goals omega

  have h5 : S ⊆ {2, 3, 5, 7, 11, 13, 17, 19} := by
    intro x hx
    have hx1 : x ∈ S := hx
    have h9 : x ≤ 20 := hS2 x hx
    have h10 : Nat.Prime x := hS1 x hx
    interval_cases x <;> norm_num at h10 ⊢
    <;> try tauto

  have h8 : S = {2, 3, 5, 7, 11, 13, 17, 19} := by
    have h9 : S ⊆ {2, 3, 5, 7, 11, 13, 17, 19} := h5
    have h10 : ({2, 3, 5, 7, 11, 13, 17, 19} : Finset ℕ).card = 8 := by native_decide
    have h11 : S.card = 8 := hS
    apply Finset.eq_of_subset_of_card_le h9
    rw [h10] at *
    all_goals omega

  rw [h8] at hS3
  norm_num [Finset.sum_insert, Finset.prod_insert] at hS3