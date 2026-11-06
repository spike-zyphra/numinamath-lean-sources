import Mathlib

theorem number_theory_16258 :
    IsLeast {b : ℕ | ∃ a : ℕ, a > 0 ∧ b > 0 ∧ (Nat.divisors a).card = 3 ∧ (Nat.divisors b).card = a ∧ a ∣ b} 8 := by
  constructor
  · -- Show 8 is in the set
    use 4
    all_goals
      native_decide
  · -- Show there is no smaller element in the set
    intro b hb
    rcases hb with ⟨a, ha_pos, hb_pos, h1, h2, hdiv⟩
    by_contra h
    push_neg at h
    have h3 : b < 8 := h
    have h4 : a ≤ 7 := by
      have h7 : a ∣ b := hdiv
      have h8 : a ≤ b := by
        exact Nat.le_of_dvd (by linarith) h7
      linarith
    interval_cases a <;> interval_cases b <;> try { 
      simp_all [Nat.divisors, Finset.card] 
      <;> try { contradiction }
    }