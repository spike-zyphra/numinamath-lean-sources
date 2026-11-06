import Mathlib

theorem number_theory_251821 : ∃ n, n ∈ Finset.Icc 1000000000 9999999999 ∧
    (Nat.digits 10 n).length = 10 ∧
    (Nat.digits 10 n).toFinset.card = 10 ∧
    11 ∣ n := by
  use 1294357680
  constructor
  · -- Show 1294357680 is in the range [1000000000, 9999999999]
    exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
  constructor
  · -- Show that the length of the digits is 10
    norm_num
  constructor
  · -- Show that the cardinality of the digits is 10 (all distinct)
    native_decide
  · -- Show 1294357680 is divisible by 11
    norm_num