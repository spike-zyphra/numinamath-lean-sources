import Mathlib

variable (p q : Nat)

def f_8665 (p q : Nat) : Int :=
  p ^ 3 + 3 * q ^ 3 - 32

/-Find all pair of primes  $(p,q)$ , such that  $p^3+3q^3-32$  is also a prime.-/
theorem number_theory_8665 :
  ∃! pair : Nat × Nat,
    let (p, q) := pair
    Prime p ∧ Prime q ∧ Prime (f_8665 p q) ∧ p = 3 ∧ q = 2 := by
  apply existsUnique_of_exists_of_unique
  · use (3, 2)
    constructor
    · apply Nat.prime_iff.1
      exact Nat.prime_three
    constructor
    · apply Nat.prime_iff.1
      exact PNat.prime_two
    constructor
    · -- Show f(3,2) is prime
      simp [f_8665]
      decide
    constructor
    · rfl
    · rfl
  · intro ⟨p1, q1⟩ ⟨p2, q2⟩ h1 h2
    rcases h1 with ⟨_, _, _, h31, h21⟩
    rcases h2 with ⟨_, _, _, h32, h22⟩
    ext
    · exact h31.trans h32.symm
    · exact h21.trans h22.symm
