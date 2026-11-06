import Mathlib

theorem number_theory_16160 : IsLeast {n : ℕ | ∃ a b : ℕ, 2 < a ∧ 2 < b ∧ Nat.ofDigits a [2, 1] = n ∧ Nat.ofDigits b  [1, 2] = n} 7 := by 
  constructor 
  · -- Show 7 is in the set using the witness a=5 and b=3
    use 5, 3
    constructor
    · norm_num 
    constructor 
    · norm_num 
    constructor 
    · simp [Nat.ofDigits]
    · simp [Nat.ofDigits]
  · -- Show that 7 is the smallest in the set
    intro n hn
    rcases hn with ⟨a, b, ha, hb, h1, h2⟩
    simp [Nat.ofDigits, List.foldl] at h1 h2
    have h3 : a + 2 = n := by linarith
    have h4 : 2 * b + 1 = n := by linarith
    have h5 : b ≥ 3 := by linarith
    omega