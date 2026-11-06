import Mathlib

theorem number_theory_258125 (p : ℕ) (hp : Odd p ∧ Nat.Prime p) (M : Finset ℕ)
    (hM : M.card = (p ^ 2 + 1) / 2) (hM1 : ∀ m ∈ M, ∃ k, m = k ^ 2) :
    ∃ S ⊆ M, S.card = p ∧ ∃ j, (S.sum id) / p = j := by
  have h2 : (p : ℕ) ≥ 2 := by 
    have hp2 := hp.2
    have : p ≥ 2 := by 
      by_contra h 
      push_neg at h 
      have : p < 2 := by omega 
      interval_cases p <;> norm_num at hp2 <;> tauto 
    omega 
  have hp2' : (p ^ 2 + 1) / 2 ≥ p := by 
    have : (p ^ 2 + 1: ℕ) ≥ 2 * p := by
      nlinarith [show p ≥ 2 by
        omega]
    omega 
  have h3 : M.card ≥ p := by 
    linarith [hM, hp2'] 
  have h4 : ∃ S ⊆ M, S.card = p := by 
    apply Finset.exists_subset_card_eq 
    all_goals linarith [h3] 
  rcases h4 with ⟨S, hS_sub, hScard⟩ 
  have h5 : ∃ j, (S.sum id) / p = j := by 
    refine' ⟨(S.sum id) / p, rfl⟩ 
  exact ⟨S, hS_sub, hScard, h5⟩