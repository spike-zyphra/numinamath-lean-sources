import Mathlib

theorem number_theory_113739 :
    {Nat.ofDigits 10 [d, c, b, a] | (a : ℕ) (b : ℕ) (c : ℕ) (d : ℕ) (_ : a ∈ Finset.Icc 1 9) (_ : b ∈ Finset.Icc 0 9) (_ : c ∈ Finset.Icc 0 9) (_ : d ∈ Finset.Icc 1 9) (_ : Nat.ofDigits 10 [d, c, b, a] = 9 * Nat.ofDigits 10 [a, b, c, d])} = {9801} := by
  ext n 
  simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First direction: if n is in the set, then n = 9801
    rintro ⟨a, b, c, d, ⟨ha1, ha2⟩, ⟨hb1, hb2⟩, ⟨hc1, hc2⟩, ⟨hd1, hd2⟩, h⟩
    simp [Nat.ofDigits] at h ⊢
    have h1 : a ≥ 1 := by linarith 
    have h2 : a ≤ 9 := by linarith
    have h3 : b ≥ 0 := by linarith 
    have h4 : b ≤ 9 := by linarith 
    have h5 : c ≥ 0 := by linarith 
    have h6 : c ≤ 9 := by linarith 
    have h7 : d ≥ 1 := by linarith 
    have h8 : d ≤ 9 := by linarith 
    interval_cases a <;> interval_cases d <;> omega
  · -- Now the reverse direction: n = 9801 is in the set
    intro h
    rw [show n = 9801 by omega]
    refine ⟨9, 8, 0, 1, ?_, ?_, ?_, ?_, ?_⟩
    all_goals 
      norm_num [Nat.ofDigits, Finset.mem_Icc]