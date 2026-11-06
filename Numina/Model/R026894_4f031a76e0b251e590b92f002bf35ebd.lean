import Mathlib

theorem number_theory_180799 (S : Finset ℕ) (hS : S.card = 5)
    (hS1 : ∀ x ∈ S, x ∈ Finset.Icc 100 999) (hS2 : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Nat.Coprime x y) :
    ∃ T ⊆ S, T.card = 4 ∧ ∀ x ∈ T, ∀ y ∈ T, x ≠ y → Nat.Coprime x y := by
  have h2 : S.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.2
    by_contra h
    rw [h] at hS
    simp at hS
  rcases h2 with ⟨x, hx⟩
  have ht_sub : (S \ {x} : Finset ℕ) ⊆ S := by 
    intro a ha 
    simp at ha ⊢ 
    tauto 
  use S \ {x}, ht_sub 
  constructor
  · -- Show T has cardinality 4 
    have ht_card : (S \ {x}).card = 4 := by
      have h4 : x ∈ S := hx 
      have h6 : ({x} : Finset ℕ) ⊆ S := by
        intro z hz
        simp at hz 
        have hyx : z = x := by 
          omega 
        rw [hyx] 
        exact hx 
      have h7 : (S \ {x}).card = S.card - ({x} : Finset ℕ).card := by 
        apply Finset.card_sdiff 
        exact h6 
      have h8 : ({x} : Finset ℕ).card = 1 := by 
        simp 
      rw [h8] at h7 
      omega 
    exact ht_card 
  · -- Show that all pairs in T are coprime 
    intro a ha b hb hab
    have ha1 : a ∈ S := by
      simp at ha ⊢ 
      tauto
    have hb1 : b ∈ S := by 
      simp at hb ⊢ 
      tauto
    have hab' : a ≠ b := hab
    have h2 := hS2 a ha1 b hb1 hab'
    exact h2