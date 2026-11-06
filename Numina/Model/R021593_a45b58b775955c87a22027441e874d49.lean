import Mathlib

theorem number_theory_96928 (a : Fin 2018 → ℕ) (ha : StrictMono a)
    (h : ∀ i, 0 < a i) (h' : ∑ i, a i = 2018 ^ 2018) :
    (∑ i, (a i) ^ 3) % 6 = 4 := by
  have h1 : ∀ i : Fin 2018, (a i) ^ 3 % 6 = (a i) % 6 := by
    intro i
    have h2 : (a i) ^ 3 % 6 = (a i) % 6 := by
      have h3 : (a i) % 6 = 0 ∨ (a i) % 6 = 1 ∨ (a i) % 6 = 2 ∨ (a i) % 6 = 3 ∨ (a i) % 6 = 4 ∨ (a i) % 6 = 5 := by
        omega
      rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3) <;> simp [h3, Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
    exact h2

  have h2 : (∑ i : Fin 2018, (a i) ^ 3) % 6 = (∑ i : Fin 2018, (a i)) % 6 := by
    simp [Finset.sum_nat_mod, h1]

  have h3 : (∑ i : Fin 2018, (a i)) = 2018 ^ 2018 := h'
  rw [h3] at h2
  rw [h2]

  have h4 : (2018 ^ 2018) % 6 = 4 := by
    norm_num [Nat.pow_mod]

  exact h4