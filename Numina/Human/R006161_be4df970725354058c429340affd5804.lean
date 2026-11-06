import Mathlib

lemma list_length_eq_four {l : List ℕ} : l.length = 4 ↔ ∃ a b c d, l = [a, b, c, d] :=
  ⟨fun _ => let [a, b, c, d] := l; ⟨a, b, c, d, rfl⟩, fun ⟨_, _, _, _, e⟩ => e ▸ rfl⟩

lemma list_length_eq_eight {l : List ℕ} : l.length = 8 ↔ ∃ a b c d e f g h, l = [a, b, c, d, e, f, g, h] :=
  ⟨fun _ => let [a, b, c, d, e, f, g, h] := l; ⟨a, b, c, d, e, f, g, h, rfl⟩, fun ⟨_, _, _, _, _, _, _, _, e⟩ => e ▸ rfl⟩

lemma finset_card_le_seven {a b c d e f g: ℕ} : ({a, b, c, d, e, f, g} :Finset ℕ).card ≤ 7 :=
  (Finset.card_insert_le _ _).trans (Nat.succ_le_succ Finset.card_le_six)


theorem my_favorite_theorem :
    IsLeast {k : ℕ | (Nat.digits 10 k).length = 8 ∧ (Nat.digits 10 k).toFinset = Finset.Icc 1 8 ∧ 99 ∣ k} 12346587 := by


  constructor
  . simp
    constructor
    . ext n
      simp
      omega
    . omega
  . simp [lowerBounds]
    intro n hn1 hn2 hn3

    rw [list_length_eq_eight] at hn1
    obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, hn1⟩ := hn1
    rw [hn1] at hn2
    simp at hn2
    by_contra hn4
    simp at hn4
    have : n7 = 1 := by
      have : n7 ∈ Finset.Icc 1 8 := by rw [← hn2]; simp
      simp at this
      have := Nat.ofDigits_digits 10 n
      rw [hn1] at this
      rw [Nat.ofDigits_eq_foldr] at this
      simp at this
      omega
    subst n7
    have : n6 = 2 := by
      have : n6 ∈ Finset.Icc 1 8 := by rw [← hn2]; simp
      simp at this
      have : n6 ≠ 1 := by
        have : (Finset.Icc 1 8).card = 8 := by simp
        rw [← hn2] at this
        by_contra h
        subst n6
        simp at this
        suffices ({n0, n1, n2, n3, n4, n5, 1}: Finset ℕ).card ≤ 7 by omega
        exact finset_card_le_seven

      have := Nat.ofDigits_digits 10 n
      rw [hn1] at this
      rw [Nat.ofDigits_eq_foldr] at this
      simp at this
      omega
    subst n6
    have : n5 = 3 := by
      have : n5 ∈ Finset.Icc 1 8 := by rw [← hn2]; simp
      simp at this
      have : n5 ≠ 1 ∧ n5 ≠ 2 := by
        by_contra h
        have : n5 = 1 ∨ n5 = 2 := by omega
        rcases this with h | h
        all_goals
        . subst n5
          have : (Finset.Icc 1 8).card = 8 := by simp
          rw [← hn2] at this
          simp at this
          suffices ({n0, n1, n2, n3, n4, 2, 1}: Finset ℕ).card ≤ 7 by omega
          exact finset_card_le_seven

      have := Nat.ofDigits_digits 10 n
      rw [hn1] at this
      rw [Nat.ofDigits_eq_foldr] at this
      simp at this
      omega
    subst n5
    have : n4 = 4 := by
      have : n4 ∈ Finset.Icc 1 8 := by rw [← hn2]; simp
      simp at this
      obtain ⟨h1, h2⟩ := this
      have : n4 ≠ 1 ∧ n4 ≠ 2 ∧ n4 ≠ 3 := by
        by_contra h
        have : n4 = 1 ∨ n4 = 2 ∨ n4 = 3 := by omega
        rcases this with h | h | h
        all_goals
        . subst n4
          have : (Finset.Icc 1 8).card = 8 := by simp
          rw [← hn2] at this
          simp at this
          suffices ({n0, n1, n2, n3, 3, 2, 1}: Finset ℕ).card ≤ 7 by omega
          exact finset_card_le_seven

      have := Nat.ofDigits_digits 10 n
      rw [hn1] at this
      rw [Nat.ofDigits_eq_foldr] at this
      simp at this
      omega
    subst n4
    have : n3 = 5 ∨ n3 = 6 := by
      have : n3 ∈ Finset.Icc 1 8 := by rw [← hn2]; simp
      simp at this
      obtain ⟨h1, h2⟩ := this
      have : n3 ≠ 1 ∧ n3 ≠ 2 ∧ n3 ≠ 3 ∧ n3 ≠ 4 := by
        by_contra h
        have : n3 = 1 ∨ n3 = 2 ∨ n3 = 3 ∨ n3 = 4 := by omega
        rcases this with h | h | h | h
        all_goals
        . subst n3
          have : (Finset.Icc 1 8).card = 8 := by simp
          rw [← hn2] at this
          simp at this
          suffices ({n0, n1, n2, 4, 3, 2, 1}: Finset ℕ).card ≤ 7 by omega
          exact finset_card_le_seven

      have := Nat.ofDigits_digits 10 n
      rw [hn1] at this
      rw [Nat.ofDigits_eq_foldr] at this
      simp at this
      omega

    rcases this with rfl | rfl
    . have h1: 6 ∈ Finset.Icc 1 8 := by simp
      have h2 : 7 ∈ Finset.Icc 1 8 := by simp
      have h3 : 8 ∈ Finset.Icc 1 8 := by simp
      rw [← hn2] at h1 h2 h3
      simp at h1 h2 h3

      rcases h1 with h1 | h1 | h1
      all_goals rcases h2 with h2 | h2 | h2
      all_goals rcases h3 with h3 | h3 | h3
      all_goals try omega
      all_goals
      . subst n0 n1 n2
        have := Nat.ofDigits_digits 10 n
        rw [hn1] at this
        rw [Nat.ofDigits_eq_foldr] at this
        simp at this
        omega
      
    . have : n2 = 5 := by
        let s1 : Finset ℕ := {n0, n1, n2}
        let s2 : Finset ℕ := {1,2,3,4,6}
        have : n2 ∈ ({5, 7, 8}:Finset ℕ) := by
          have : s1.card ≤ 3 := Finset.card_le_three
          have : s2.card = 5 := by unfold s2; simp
          have : ({n0, n1, n2, 6, 4, 3, 2, 1}) = s1 ∪ s2 := by
            unfold s1 s2
            ext x
            simp
            omega
          
          rw [hn2] at this
          have : (s1 ∪ s2).card = 8 := by
            rw [← this]
            simp
          rw [Finset.card_union] at this
          have hs: (s1 ∩ s2).card = 0 := by omega
          simp at hs

          rw [show {5, 7, 8} = Finset.Icc 1 8 \ {1,2,3,4,6} by native_decide]
          rw [← hn2]
          rw [Finset.mem_sdiff]
          refine ⟨?_, ?_⟩
          . simp
          . by_contra h
            have : n2 ∈ s2 := h
            have : n2 ∈ s1 := by unfold s1; simp
            have : n2 ∈ s1 ∩ s2 := by simp; constructor <;> assumption
            rw [hs] at this
            simp at this

        simp at this
        rcases this with h | h | h
        . exact h
        . have := Nat.ofDigits_digits 10 n
          rw [hn1] at this
          rw [Nat.ofDigits_eq_foldr] at this
          simp at this
          omega
        . have := Nat.ofDigits_digits 10 n
          rw [hn1] at this
          rw [Nat.ofDigits_eq_foldr] at this
          simp at this
          omega

      subst n2
      have : n1 = 7 := by
        have : 7 ∈ Finset.Icc 1 8 := by simp
        rw [← hn2] at this
        simp at this
        rcases this with h | h
        . symm at h
          subst n0
          have : 8 ∈ Finset.Icc 1 8 := by simp
          rw [← hn2] at this
          simp at this
          symm at this
          subst n1
          have : n = 12346587 := by
            rw [← Nat.ofDigits_digits 10 n]
            rw [hn1]
            decide
          omega
        . exact h.symm
      subst n1
      have : n0 = 8 := by
        have : 8 ∈ Finset.Icc 1 8 := by simp
        rw [← hn2] at this
        simp at this
        exact this.symm
      subst n0
      have : n = 12346578 := by
        rw [← Nat.ofDigits_digits 10 n]
        rw [hn1]
        decide
      omega
