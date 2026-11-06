import Mathlib

/-How many times does 24 divide into 100 ! (factorial)?-/
theorem number_theory_610850: (24 ^ 32 ∣ Nat.factorial 100) ∧ (¬ 24 ^ 33 ∣ Nat.factorial 100) := by
    constructor
    -- show that 24^32 divides 100! --
    . simp [Nat.factorial]
      norm_num
    -- show that 24^33 does not divide 100! --
    . simp [Nat.factorial]
      norm_num