import Mathlib

open Nat

theorem number_theory_116226 {p : ℕ} (hp : p ≠ 1) :
    Nat.Prime p ↔ ((p - 1) ! : ZMod p) = -1 := by
  by_cases hp0 : p = 0
  · -- case p = 0
    rw [hp0]
    simp [Nat.prime_def_lt, Nat.factorial]
    <;> try tauto <;> try aesop
  · -- case p ≠ 0
    have hp0' : p ≠ 0 := by 
      intro h
      apply hp0
      omega
    have hp2 : p ≥ 2 := by 
      by_contra h
      push_neg at h
      have : p < 2 := by linarith
      interval_cases p <;> try tauto 
    have h8 : Nat.Prime p ↔ ((p - 1) ! : ZMod p) = -1 := by 
      apply Nat.prime_iff_fac_equiv_neg_one
      all_goals linarith 
    exact h8