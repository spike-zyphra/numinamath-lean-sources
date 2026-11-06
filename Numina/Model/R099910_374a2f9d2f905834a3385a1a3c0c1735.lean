import Mathlib

theorem number_theory_246050 :
    101 ∣ ∑ n in (Finset.Icc 1 9999).filter (fun n => (n / 100) % 100 = n % 100), n := by
  native_decide