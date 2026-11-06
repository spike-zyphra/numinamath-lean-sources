import Mathlib

theorem number_theory_161268 (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 108)
    (h1 : ∀ a ∈ S, ∀ b ∈ S, ∃ c ∈ S, Nat.gcd a c = 1 ∧ Nat.gcd b c = 1)
    (h2 : ∀ a ∈ S, ∀ b ∈ S, ∃ c' ∈ S, Nat.gcd a c' > 1 ∧ Nat.gcd b c' = 1) :
    S.card ≤ 76 := by
  have h3 : S = ∅ := by
    have h4 : ∀ a ∈ S, ∀ b ∈ S, ∃ c' ∈ S, Nat.gcd a c' > 1 ∧ Nat.gcd b c' = 1 := h2
    by_contra h
    have h6 : S.Nonempty := by
      have : S.Nonempty := by
        by_contra h'
        simp at h'
        tauto
      assumption
    rcases h6 with ⟨a, ha⟩
    have h7 := h4 a ha a ha
    rcases h7 with ⟨c', hc', h8, h9⟩
    have h10 : Nat.gcd a c' > 1 := h8
    have h11 : Nat.gcd a c' = 1 := h9
    omega
  rw [h3]
  simp