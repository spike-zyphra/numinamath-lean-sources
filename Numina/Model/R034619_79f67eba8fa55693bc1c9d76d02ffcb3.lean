import Mathlib

theorem number_theory_15776 : Set.encard {p : ℕ | 7 < p ∧ p.Prime ∧ Nat.ofDigits p [7, 0, 0, 1] +
    Nat.ofDigits p [6, 0, 3] + Nat.ofDigits p [3, 1, 1] + Nat.ofDigits p [5, 2, 1] +
    Nat.ofDigits p [6] = Nat.ofDigits p [2, 4, 1] + Nat.ofDigits p [1, 7, 2] +
    Nat.ofDigits p [0, 6, 3]} = 0 := by 
  have h1 : {p : ℕ | 7 < p ∧ p.Prime ∧ Nat.ofDigits p [7, 0, 0, 1] +
      Nat.ofDigits p [6, 0, 3] + Nat.ofDigits p [3, 1, 1] + Nat.ofDigits p [5, 2, 1] +
      Nat.ofDigits p [6] = Nat.ofDigits p [2, 4, 1] + Nat.ofDigits p [1, 7, 2] +
      Nat.ofDigits p [0, 6, 3]} = ∅ := by 
    ext p 
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hp
    rcases hp with ⟨hp1, hp2, heq⟩
    simp [Nat.ofDigits, pow_succ, pow_zero, mul_assoc, Nat.mul_comm] at heq
    <;> try { 
      have h2 : p ≥ 8 := by omega 
      nlinarith [show p ≥ 8 by omega, hp2] 
    } 
  rw [h1]
  simp