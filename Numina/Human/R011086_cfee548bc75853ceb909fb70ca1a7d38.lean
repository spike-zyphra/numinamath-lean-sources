import Mathlib

/- The increasing sequence 2,3,5,6,7,10,11,… consists of all positive integers that are neither the  square nor the  cube of a positive integer. Find the 500th term of this sequence. -/

open Finset

theorem number_theory_95566 :
(Nat.nth {x | x > 0 ∧  ¬(∃ n, x = n^2) ∧ ¬(∃ n, x = n^3)} 499) = 528 := by
  /- Because there aren't that many perfect squares or cubes, let's look for the smallest perfect square greater than 500. This happens to be 23^2 = 529. Notice that there are 23 squares and 8 cubes less than or equal to 529, but 1 and 2^6 are both squares and cubes. Thus, there are 529−23−8+2=500 numbers in our sequence less than 529.  Magically, we want the 500th term, so our answer is the biggest non-square and non-cube less than 529, which is 528. -/
  -- Let S be the set containing all numbers in our sequence. We show that there are 499 numbers smaller than 528 in our sequence, and that 528 is in our sequence, which then implies that the 500 number in the sequence is 528
  let S := {x | x > 0 ∧ ¬(∃ n, x = n^2) ∧ ¬(∃ n, x = n^3)}
  let f₁ : ℕ ↪ ℕ := ⟨fun x : ℕ ↦ x ^ 2, by simp [Function.Injective]⟩
  let f₂ : ℕ ↪ ℕ := ⟨fun x : ℕ ↦ x ^ 3, by simp [Function.Injective]⟩
  -- The numbers smaller than 528 that appear in S are exactly the numbers that are not a square of of a number smaller than 23 and not a cube of a number smaller than 8.
  have h : ∀ x ∈ Finset.range 528, S x ↔
      ¬ x ∈ (Finset.map f₁ (Finset.range 23) ∪ Finset.map f₂ (Finset.range 9)) := by
    intro x hx
    apply Iff.intro
    · intro ⟨hx ,h2, h3⟩
      simp_all [S, f₁, f₂]
      apply And.intro
      · intro n hn heq
        subst heq
        simp_all
      · intro n hn heq
        subst heq
        simp_all
    · intro h
      simp_all [S,f₁, f₂]
      apply And.intro
      · apply Nat.zero_lt_of_ne_zero
        apply Ne.symm
        have : ¬0 ^ 2 = x := h.1 0 (by simp)
        simp_all
      rcases h with ⟨h2,h3⟩
      apply And.intro
      · intro n x_eq
        subst x_eq
        simp[pow_left_inj₀] at h2
        have heq : 23 ≤ n := by
          rw[← not_lt]
          intro hx
          apply h2 n hx
          rfl
        have := Nat.mul_self_le_mul_self heq
        linarith
      · intro n x_eq
        subst x_eq
        simp[pow_left_inj₀] at h3
        have heq : 9 ≤ n := by
          rw[← not_lt]
          intro hx
          apply h3 n hx
          rfl
        have :=  mul_le_mul_three heq heq heq
        simp_all
        linarith
  have : DecidablePred S := by
    simp [DecidablePred]
    intro n
    exact Classical.propDecidable (S n)
  have : DecidablePred (fun x ↦ ¬ (x ∈ {n^2 | n : ℕ} ∨ x ∈ {n^3 | n : ℕ})) := by
    simp [DecidablePred]
    intro n
    apply Classical.propDecidable
  have hf₁ : range 528 ∩ map f₁ (range 23) = map f₁ (range 23) := by
    apply subset_antisymm
    · apply inter_subset_right
    · rw [← inter_self (map f₁ (range 23))]
      apply inter_subset_inter_right
      intro x hx
      simp_all [f₁]
      rcases hx with ⟨a,⟨ha,hxeq⟩⟩
      subst hxeq
      apply Nat.add_one_le_iff.2 at ha
      simp at ha
      have := Nat.mul_self_le_mul_self ha
      linarith
  have hf₂ : range 528 ∩ map f₂ (range 9) = map f₂ (range 9) := by
    apply subset_antisymm
    · apply inter_subset_right
    · rw [← inter_self (map f₂ (range 9))]
      apply inter_subset_inter_right
      intro x hx
      simp_all [f₂]
      rcases hx with ⟨a,⟨ha,hxeq⟩⟩
      subst hxeq
      apply Nat.add_one_le_iff.2 at ha
      simp at ha
      have := mul_le_mul_three ha ha ha
      linarith
  -- There are three numbers which are both a square of a number smaller than 23 and a cube of a number smaller than 9, namely 0, 1 and 2^6.
  have hf₁f₂ : #(map f₁ (range 23) ∩ map f₂ (range 9)) = 3 := by
    simp[f₁, f₂, map]
  -- Therefore the there are 528 - 23 - 9 + 3 = 499 numbers smaller than 528 in our sequence.
  have h_count : Nat.count S 528 = 499 := by
    rw [Nat.count_eq_card_filter_range]
    rw [filter_congr h]
    rw [filter_not]
    have filter_mem: ∀ s t : Finset ℕ, filter (Membership.mem s) t = t ∩ s := by
      intro s t
      ext a
      simp_all only [mem_filter, mem_inter]
    rw [card_sdiff (by simp)]
    rw [filter_mem]
    rw [inter_union_distrib_left]
    rw [hf₁, hf₂]
    rw [card_union]
    rw [hf₁f₂]
    simp [Finset.card_map]
  -- As we stated before 528 is in our sequence, which as explained before implies that it is the 500 element of the sequence.
  have h528 : S 528 := by
    unfold S
    simp_all [S]
    apply And.intro
    · simp
    · apply And.intro
      · have  : ¬∃ x, x ^ 2 = 528 := by
          apply @Nat.not_exists_sq' 22
          · linarith
          · linarith
        aesop
      · intro n hn
        rcases Nat.lt_or_ge n 9 with h_lt | h_ge
        · apply Nat.add_one_le_iff.2 at h_lt
          simp at h_lt
          have := mul_le_mul_three h_lt h_lt h_lt
          linarith
        · have := mul_le_mul_three h_ge h_ge h_ge
          linarith
  rw [← h_count]
  exact Nat.nth_count h528