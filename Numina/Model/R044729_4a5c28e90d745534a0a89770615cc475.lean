import Mathlib
set_option maxHeartbeats 0

theorem number_theory_258951 :
    IsGreatest {n | (Nat.digits 10 n).Nodup ∧ 8 ∣ Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))} 8697543210 := by
  constructor
  · norm_num [Nat.ofDigits]
  · intro n h
    simp at h
    obtain ⟨h₀, h₁⟩ := h
    by_contra! hn
    have h₂ : (Nat.digits 10 n).length = 10 := by
      apply le_antisymm
      . rw [<-List.toFinset_card_of_nodup h₀]
        change (Nat.digits 10 n).toFinset.card ≤ (Finset.range 10).card
        apply Finset.card_le_card
        rw [Finset.subset_iff]
        intro k hk
        simp at hk ⊢
        apply Nat.digits_lt_base (by norm_num) hk
      . calc
          _ ≥ (Nat.digits 10 8697543210).length := by
            apply Nat.le_digits_len_le _ _ _ (le_of_lt hn)
          _ = 10 := by
            norm_num
    have lm {l : List ℕ} :
        l.length = 10 → ∃ a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉, l = [a₀, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉] :=
      fun _ => let [a₀, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉] := l; ⟨a₀, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, rfl⟩
    obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, h₃⟩ := lm h₂
    have h₄ := Nat.ofDigits_digits 10 n
    simp [h₃, Nat.ofDigits] at h₁ h₄
    have h₅ : a₀ < 10 ∧ a₁ < 10 ∧ a₂ < 10 ∧ a₃ < 10 ∧ a₄ < 10 ∧ a₅ < 10 ∧ a₆ < 10 ∧ a₇ < 10 ∧ a₈ < 10 ∧ a₉ < 10 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals
        apply @Nat.digits_lt_base 10 n _ (by norm_num)
        simp [h₃]
    simp [h₃] at h₀
    have : a₉ = 8 := by
      omega
    subst a₉
    have : a₈ = 6 := by
      omega
    subst a₈
    have : a₇ = 9 := by
      omega
    subst a₇
    have : a₆ = 7 := by
      omega
    subst a₆
    have : a₅ = 5 := by
      omega
    subst a₅
    have : a₄ = 4 := by
      omega
    subst a₄
    simp [h₃] at h₀
    have : a₃ = 3 := by
      omega
    subst a₃
    have : a₂ = 2 := by
      omega
    subst a₂
    have : a₁ = 1 := by
      omega
    subst a₁
    have : a₀ = 0 := by
      omega
    subst a₀
    norm_num [h₃, Nat.ofDigits, List.reverse] at h₁ h₄ ⊢
    all_goals
      omega