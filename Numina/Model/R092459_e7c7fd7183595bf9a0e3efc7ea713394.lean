import Mathlib

theorem number_theory_206650 : ∃ n, 2020 ∣ n ∧ ∀ i ∈ Finset.range 10, (Nat.digits 10 n).count i = (Nat.digits 10 n).length / 10 := by
  use 10198987676545432320
  constructor
  · norm_num
  · intro i hi
    fin_cases hi <;> norm_num [Finset.mem_range, Nat.digits, Nat.digitsAux] at *