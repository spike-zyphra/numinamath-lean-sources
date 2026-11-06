import Mathlib

open Finset

/-
A deck of playing cards, excluding the joker, has 4 suits totaling 52 cards, with each suit having 13 cards, numbered from 1 to 13. Feifei draws 2 hearts, 3 spades, 4 diamonds, and 5 clubs. If the sum of the face values of these 14 cards Feifei drew is exactly 35, then how many of them are 1? 
-/

theorem number_theory_104565
    (has_heart : ℕ → ℕ) (has_spade : ℕ → ℕ) (has_diamond : ℕ → ℕ) (has_club : ℕ → ℕ)
    (has_heart_le : ∀ i ∈ Icc 1 13, has_heart i ≤ 1)
    (has_spade_le : ∀ i ∈ Icc 1 13, has_spade i ≤ 1)
    (has_diamond_le : ∀ i ∈ Icc 1 13, has_diamond i ≤ 1)
    (has_club_le : ∀ i ∈ Icc 1 13, has_club i ≤ 1)
    (card_has_heart : #{i ∈ Icc 1 13 | has_heart i = 1} = 2)
    (card_has_spade : #{i ∈ Icc 1 13 | has_spade i = 1} = 3)
    (card_has_diamond : #{i ∈ Icc 1 13 | has_diamond i = 1} = 4)
    (card_has_club : #{i ∈ Icc 1 13 | has_club i = 1} = 5)
    (sum_values : ∑ i ∈ Icc 1 13 with has_heart i = 1, i
      + ∑ i ∈ Icc 1 13 with has_spade i = 1, i
      + ∑ i ∈ Icc 1 13 with has_diamond i = 1, i
      + ∑ i ∈ Icc 1 13 with has_club i = 1, i
      = 35)
    : has_heart 1 + has_spade 1 + has_diamond 1 + has_club 1 = 4 := by

  have sum_Ico_card_le_sum_of_monotoneOn
      {α : Type _} [Preorder α] [AddCommMonoid α] [AddLeftMono α]
      (a b : ℕ) (s : Finset ℕ) (hs : s ⊆ Icc a b) (f : ℕ → α) (hf : MonotoneOn f (Icc a b)) :
      ∑ i ∈ Ico a (a + s.card), f i ≤ ∑ i ∈ s, f i := by
    induction' hs2 : s.card with n ih generalizing s
    . simp [card_eq_zero] at hs2
      simp [hs2]
    . obtain ⟨j, hj1, hj2⟩ : ∃ j ∈ s, j ≥ a + n := by
        by_contra h
        push_neg at h
        replace h : s ⊆ Ico a (a + n) := by
          intro x hx
          specialize hs hx
          specialize h x hx
          simp at hs ⊢; omega
        replace h := card_le_card h
        simp at h
        omega
      have c1 := card_le_card hs
      simp at c1
      have h1 : {a + n} ⊆ Ico a (a + (n + 1 : ℕ)) := by intro k; simp; omega
      rw [←sum_sdiff h1]
      replace h1 : Ico a (a + (n + 1 : ℕ)) \ {a + n} = Ico a (a + n) := by ext k; simp; omega
      rw [h1]
      replace h1 : {j} ⊆ s := by intro k hk; simp at hk; subst hk; exact hj1
      rw [←sum_sdiff h1]
      iterate 2 rw [sum_singleton]
      have h2 : f (a + n) ≤ f j := hf (by simp; omega) (hs hj1) hj2
      specialize ih (s \ {j})
        (by intro k hk; simp at hk; exact hs hk.1)
        (by simp [card_sdiff h1]; omega)
      exact add_le_add ih h2

  set sum_hearts := ∑ i ∈ Icc 1 13 with has_heart i = 1, i
  set sum_spades := ∑ i ∈ Icc 1 13 with has_spade i = 1, i
  set sum_diamonds := ∑ i ∈ Icc 1 13 with has_diamond i = 1, i
  set sum_clubs := ∑ i ∈ Icc 1 13 with has_club i = 1, i

  set owned_hearts := {i ∈ Icc 1 13 | has_heart i = 1}
  set owned_spades := {i ∈ Icc 1 13 | has_spade i = 1}
  set owned_diamonds := {i ∈ Icc 1 13 | has_diamond i = 1}
  set owned_clubs := {i ∈ Icc 1 13 | has_club i = 1}

  have h1 (c1 : has_heart 1 = 0) : sum_hearts ≥ 5 := calc
    _ ≥ ∑ i ∈ Ico 2 4, i := by
      have c2 : owned_hearts ⊆ Icc 2 13 := by
        intro k hk
        simp [owned_hearts] at hk
        by_cases hk2 : k = 1
        . subst hk2; omega
        . simp; omega
      have c3 := sum_Ico_card_le_sum_of_monotoneOn _ _ owned_hearts c2 id monotoneOn_id
      simpa [card_has_heart] using c3
    _ = _ := by decide

  have h1' : sum_hearts ≥ 3 := calc
    _ ≥ ∑ i ∈ Ico 1 3, i := by
      have c2 : owned_hearts ⊆ Icc 1 13 := by intro k hk; simp [owned_hearts] at hk ⊢; omega
      have c3 := sum_Ico_card_le_sum_of_monotoneOn _ _ owned_hearts c2 id monotoneOn_id
      simpa [card_has_heart] using c3
    _ = _ := by decide

  have h2 (c1 : has_spade 1 = 0) : sum_spades ≥ 9 := calc
    _ ≥ ∑ i ∈ Ico 2 5, i := by
      have c2 : owned_spades ⊆ Icc 2 13 := by
        intro k hk
        simp [owned_spades] at hk
        by_cases hk2 : k = 1
        . subst hk2; omega
        . simp; omega
      have c3 := sum_Ico_card_le_sum_of_monotoneOn _ _ owned_spades c2 id monotoneOn_id
      simpa [card_has_spade] using c3
    _ = _ := by decide

  have h2' : sum_spades ≥ 6 := calc
    _ ≥ ∑ i ∈ Ico 1 4, i := by
      have c2 : owned_spades ⊆ Icc 1 13 := by intro k hk; simp [owned_spades] at hk ⊢; omega
      have c3 := sum_Ico_card_le_sum_of_monotoneOn _ _ owned_spades c2 id monotoneOn_id
      simpa [card_has_spade] using c3
    _ = _ := by decide

  have h3 (c1 : has_diamond 1 = 0) : sum_diamonds ≥ 14 := calc
    _ ≥ ∑ i ∈ Ico 2 6, i := by
      have c2 : owned_diamonds ⊆ Icc 2 13 := by
        intro k hk
        simp [owned_diamonds] at hk
        by_cases hk2 : k = 1
        . subst hk2; omega
        . simp; omega
      have c3 := sum_Ico_card_le_sum_of_monotoneOn _ _ owned_diamonds c2 id monotoneOn_id
      simpa [card_has_diamond] using c3
    _ = _ := by decide

  have h3' : sum_diamonds ≥ 10 := calc
    _ ≥ ∑ i ∈ Ico 1 5, i := by
      have c2 : owned_diamonds ⊆ Icc 1 13 := by intro k hk; simp [owned_diamonds] at hk ⊢; omega
      have c3 := sum_Ico_card_le_sum_of_monotoneOn _ _ owned_diamonds c2 id monotoneOn_id
      simpa [card_has_diamond] using c3
    _ = _ := by decide

  have h4 (c1 : has_club 1 = 0) : sum_clubs ≥ 20 := calc
    _ ≥ ∑ i ∈ Ico 2 7, i := by
      have c2 : owned_clubs ⊆ Icc 2 13 := by
        intro k hk
        simp [owned_clubs] at hk
        by_cases hk2 : k = 1
        . subst hk2; omega
        . simp; omega
      have c3 := sum_Ico_card_le_sum_of_monotoneOn _ _ owned_clubs c2 id monotoneOn_id
      simpa [card_has_club] using c3
    _ = _ := by decide

  have h4' : sum_clubs ≥ 15 := calc
    _ ≥ ∑ i ∈ Ico 1 6, i := by
      have c2 : owned_clubs ⊆ Icc 1 13 := by intro k hk; simp [owned_clubs] at hk ⊢; omega
      have c3 := sum_Ico_card_le_sum_of_monotoneOn _ _ owned_clubs c2 id monotoneOn_id
      simpa [card_has_club] using c3
    _ = _ := by decide

  have h5 : has_heart 1 = 1 := by specialize has_heart_le 1 (by simp); omega
  have h6 : has_spade 1 = 1 := by specialize has_spade_le 1 (by simp); omega
  have h7 : has_diamond 1 = 1 := by specialize has_diamond_le 1 (by simp); omega
  have h8 : has_club 1 = 1 := by specialize has_club_le 1 (by simp); omega

  have h9 : has_heart 1 + has_spade 1 + has_diamond 1 + has_club 1 = 4 := by omega
  exact h9
