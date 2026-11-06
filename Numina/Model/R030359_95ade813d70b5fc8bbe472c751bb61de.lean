import Mathlib

open Finset

theorem number_theory_632030 (a b c : ℕ) (ha : a ∈ Icc 1 9) (hb : b ∈ Icc 1 9) (hc : c ∈ Icc 1 9) (h : Nat.ofDigits 10 [a, 2] * Nat.ofDigits 10 [c, b, 3] = 6657) : Nat.ofDigits 10 [c, b, a] = 117 := by

  simp [Nat.ofDigits, Finset.mem_Icc] at h ha hb hc ⊢

  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩
  rcases hc with ⟨hc1, hc2⟩
  interval_cases a <;> interval_cases b <;> interval_cases c
  <;> omega