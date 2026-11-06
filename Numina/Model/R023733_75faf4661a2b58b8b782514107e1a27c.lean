import Mathlib

theorem number_theory_68049 (a : Fin 9 → ℕ) (ha : ∀ i, a i % 100 = i + 11) :
    (∑ i, a i ^ 2) % 100 = 85 := by
  have h1 : a 0 % 100 = 11 := by
    specialize ha 0
    simpa using ha
  have h2 : a 1 % 100 = 12 := by
    specialize ha 1
    simpa using ha
  have h3 : a 2 % 100 = 13 := by
    specialize ha 2
    simpa using ha
  have h4 : a 3 % 100 = 14 := by
    specialize ha 3
    simpa using ha
  have h5 : a 4 % 100 = 15 := by
    specialize ha 4
    simpa using ha
  have h6 : a 5 % 100 = 16 := by
    specialize ha 5
    simpa using ha
  have h7 : a 6 % 100 = 17 := by
    specialize ha 6
    simpa using ha
  have h8 : a 7 % 100 = 18 := by
    specialize ha 7
    simpa using ha
  have h9 : a 8 % 100 = 19 := by
    specialize ha 8
    simpa using ha
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at *
  have h10 : a 0 ^ 2 % 100 = 21 := by
    have h11 : a 0 % 100 = 11 := h1
    simp [Nat.pow_mod, h11]
  have h11 : a 1 ^ 2 % 100 = 44 := by
    have h12 : a 1 % 100 = 12 := h2
    simp [Nat.pow_mod, h12]
  have h12 : a 2 ^ 2 % 100 = 69 := by
    have h13 : a 2 % 100 = 13 := h3
    simp [Nat.pow_mod, h13]
  have h13 : a 3 ^ 2 % 100 = 96 := by
    have h14 : a 3 % 100 = 14 := h4
    simp [Nat.pow_mod, h14]
  have h14 : a 4 ^ 2 % 100 = 25 := by
    have h15 : a 4 % 100 = 15 := h5
    simp [Nat.pow_mod, h15]
  have h15 : a 5 ^ 2 % 100 = 56 := by
    have h16 : a 5 % 100 = 16 := h6
    simp [Nat.pow_mod, h16]
  have h16 : a 6 ^ 2 % 100 = 89 := by
    have h17 : a 6 % 100 = 17 := h7
    simp [Nat.pow_mod, h17]
  have h17 : a 7 ^ 2 % 100 = 24 := by
    have h18 : a 7 % 100 = 18 := h8
    simp [Nat.pow_mod, h18]
  have h18 : a 8 ^ 2 % 100 = 61 := by
    have h19 : a 8 % 100 = 19 := h9
    simp [Nat.pow_mod, h19]
  omega