import Mathlib

theorem number_theory_71765 (a : ℕ → ℕ)
    (h₀ : a 1 = 1)
    (h₁ : a 2 = 2)
    (h₂ : ∀ n, a (n + 1) = sSup {p | p.Prime ∧ p ∣ ∑ i in Finset.Icc 1 n, a i}) :
    a 100 = 53 := by
  have h5 := h₂ 1
  have h6 : ∑ i in Finset.Icc 1 1, a i = 1 := by
    simp [Finset.sum_singleton, h₀]
  have h5' : a 2 = sSup {p : ℕ | p.Prime ∧ p ∣ 1} := by
    rw [h5]
    rw [h6]
    <;> norm_num [Finset.sum_singleton]
    <;> try tauto
    all_goals norm_num
  have h_zero : sSup {p : ℕ | p.Prime ∧ p ∣ 1} = 0 := by
    have : {p : ℕ | p.Prime ∧ p ∣ 1} = ∅ := by
      ext p
      simp
      all_goals intro hp
      have : p ≥ 2 := Nat.Prime.two_le hp
      omega
    rw [this]
    simp
  rw [h_zero] at h5'
  omega