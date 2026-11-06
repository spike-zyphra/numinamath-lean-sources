import Mathlib

theorem number_theory_306812 (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    ∃ x : ℕ, x > 0 ∧ ∃ a b c d : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧
      x = a ^ c + b ^ d ∧ Nat.Prime c ∧ Nat.Prime d ↔
    ∀ p ∈ P, Nat.Prime p := by
  -- first prove a simple equivalence when given `t` as a Finset 
  -- convert both sides with balls and another side with generated witnesses to prove bicondition or tauto
  use 8
  constructor
  · -- show x > 0. 
    norm_num
  · -- pick 8 as one sum: 2^2 + 2^2 as Nat.Prime (Nat.succ = succ 1 > 0) ) > 0 and showing 1 ^ n n n n n P.
    use 2, 2, 2, 2
    have hp2 : Nat.Prime 2 := by norm_num
    simp [hp2, hP]
    <;> aesop <;> try { tauto }