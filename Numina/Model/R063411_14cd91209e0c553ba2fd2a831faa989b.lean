import Mathlib

theorem number_theory_161066 (n : ℕ) :
    n ∈ {n | n ∈ Finset.Icc 100 999 ∧ n = 5 * (Nat.digits 10 n).prod} ↔ n = 175 := by
  constructor
  · -- Assume n ∈ {n | n ∈ Finset.Icc 100 999 ∧ n = 5 * (Nat.digits 10 n).prod}, prove n = 175
    intro h
    rcases h with ⟨hn1, hn2⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨h1, h2⟩
    interval_cases n <;> norm_num at hn2 ⊢ <;> tauto
    all_goals omega
  · -- Assume n = 175, prove n ∈ {n | n ∈ Finset.Icc 100 999 ∧ n = 5 * (Nat.digits 10 n).prod}
    intro h
    rw [h]
    constructor
    · -- Show that 175 ∈ Finset.Icc 100 999
      exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    · -- Show that 175 = 5 * (Nat.digits 10 175).prod
      norm_num