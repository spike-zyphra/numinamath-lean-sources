import Mathlib

theorem number_theory_83871 :
    IsLeast {k | ∃ s : Multiset ℤ, Multiset.card s = k ∧ (s.map (λx ↦ x^2)).sum = 2010} 3 := by
  constructor
  · -- Show 3 is achievable
    use {44, 7, 5}
    native_decide
  · -- Show minimality of 3
    intro k hk
    rcases hk with ⟨s, hk1, hk2⟩
    by_contra h
    push_neg at h
    have h1 : k < 3 := by linarith
    have h2 : Multiset.card s < 3 := by
      calc
        Multiset.card s = k := by linarith [hk1]
        _ < 3 := by linarith [h1]
    have h4 : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 := by 
      omega
    rcases h4 with h4 | h4 | h4
    · -- Case where k = 0
      have h5 : s = ∅ := by 
        simp [Multiset.card_eq_zero] at h4 ⊢
        exact h4
      rw [h5] at hk2
      simp [Multiset.sum_eq_zero] at hk2
    · -- Case where k = 1
      have h5 : s.card = 1 := h4
      obtain ⟨x, hx⟩ := Multiset.card_eq_one.1 h4
      rw [hx] at hk2
      simp at hk2
      have h6 : x^2 = 2010 := by 
        linarith
      have h7 : x ≤ 44 := by nlinarith
      have h8 : x ≥ -45 := by nlinarith
      interval_cases x <;> omega
    · -- Case where k = 2
      have h5 : s.card = 2 := h4
      obtain ⟨x, y, hx⟩ := Multiset.card_eq_two.1 h4
      rw [hx] at hk2
      simp at hk2
      have h6 : x^2 + y^2 = 2010 := by 
        linarith
      have h7 : x ≤ 44 := by nlinarith [sq_nonneg y]
      have h8 : y ≤ 44 := by nlinarith [sq_nonneg x]
      have h9 : x ≥ -45 := by nlinarith [sq_nonneg y]
      have h10 : y ≥ -45 := by nlinarith [sq_nonneg x]
      interval_cases x <;> interval_cases y <;> omega