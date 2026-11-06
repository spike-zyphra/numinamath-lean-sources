import Mathlib

def isFriendly (n : ℕ) : Prop :=
  ∀ i, (Nat.digits 10 n)[i]! + 1 = (Nat.digits 10 n)[i + 1]! ∨
    (Nat.digits 10 n)[i]! - 1 = (Nat.digits 10 n)[i + 1]!

theorem number_theory_32695 :
    {m | Odd m ∧ ∃ n, isFriendly n ∧ 64 * m ∣ n} = {m | Odd m} := by
  ext m
  simp only [Set.mem_setOf_eq]
  constructor
  · -- Assume m is in the left side, so m is odd and there exists a friendly n divisible by 64m
    rintro ⟨hodd, n, hfriendly, hdiv⟩
    exact hodd
  · -- Assume m is odd
    intro hodd
    constructor
    · exact hodd
    · -- We need to show that there exists a friendly n such that 64 * m divides n
      use 0
      constructor
      · -- Show that 0 is friendly
        intro i
        simp [isFriendly]
      · -- Show that 64 * m divides 0
        simp
        <;> omega