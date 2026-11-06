import Mathlib

theorem number_theory_8162 :
    (∃ x, x ≡ 3 [MOD 7] ∧ 6 * x ≡ 10 [MOD 8]) ∧
    ¬∃ x, 3 * x ≡ 1 [MOD 10] ∧ 4 * x ≡ 7 [MOD 15] := by
  constructor
  · -- Show that x = 3 is a solution to the first system
    use 3
    constructor
    · norm_num [Nat.ModEq]
    · norm_num [Nat.ModEq]
  · -- Show that the second system has no solution
    intro h
    rcases h with ⟨x, hx1, hx2⟩
    norm_num [Nat.ModEq] at hx1 hx2
    omega