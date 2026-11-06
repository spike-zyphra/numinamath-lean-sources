import Mathlib

theorem number_theory_304157 :
    ∃ n : ℕ, 1997 ∣ n ∧ n < 10^11 ∧ ∀ d ∈ Nat.digits 10 n, d ≠ 2 ∧ d ≠ 3 ∧ d ≠ 4 ∧ d ≠ 5 ∧ d ≠ 6 ∧ d ≠ 7 := by
  use 0
  constructor
  · -- Show that 0 is divisible by 1997
    norm_num
  constructor
  · -- Show that 0 < 10^11
    norm_num
  intro d hd
  simp_all