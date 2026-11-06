import Mathlib

theorem number_theory_309703 :
    ∃ n : ℕ, n ∈ Finset.Icc 1000 9999 ∧ n^2 ≡ n [MOD 10000] ∧
    ∃ m : ℕ, m ∈ Finset.Icc 10000 99999 ∧ m^2 ≡ m [MOD 100000] := by
  use 9376
  constructor
  · -- Show that 9376 is in the range [1000, 9999]
    simp [Finset.mem_Icc]
  constructor
  · -- Show 9376^2 ≡ 9376 [MOD 10000]
    norm_num [Nat.ModEq]
  · -- Show existence of the five-digit number.
    use 90625
    constructor
    · -- Show that 90625 is in the range [10000, 99999]
      simp [Finset.mem_Icc]
    · -- Show 90625^2 ≡ 90625 [MOD 100000]
      norm_num [Nat.ModEq]