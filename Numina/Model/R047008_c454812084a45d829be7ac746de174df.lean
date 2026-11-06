import Mathlib

theorem number_theory_184752 (n : ℕ) (a : Fin n → ℤ) (h : ∑ i : Fin n, a i ≡ 0 [ZMOD 6]) :
    ∑ i : Fin n, (a i)^3 ≡ 0 [ZMOD 6] := by
  have h1 : ∀ i : Fin n, (a i) ^ 3 % 6 = (a i) % 6 := by
    intro i
    have h2 : (a i) % 6 = 0 ∨ (a i) % 6 = 1 ∨ (a i) % 6 = 2 ∨ (a i) % 6 = 3 ∨ (a i) % 6 = 4 ∨ (a i) % 6 = 5 := by
      omega
    rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2) <;> simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
  have h2 : (∑ i : Fin n, (a i)^3) % 6 = (∑ i : Fin n, a i) % 6 := by
    simp [Finset.sum_int_mod, h1]
  have h3 : (∑ i : Fin n, (a i)^3) % 6 = 0 := by
    have h4 : (∑ i : Fin n, (a i)^3) % 6 = (∑ i : Fin n, a i) % 6 := h2
    have h5 : (∑ i : Fin n, a i) % 6 = 0 := by
      simp [Int.ModEq] at h ⊢
      omega
    omega
  simp [Int.ModEq]
  omega