import Mathlib

theorem number_theory_609 :
    ((Finset.Icc 10000 99999).filter
        fun n => 6 ∣ n ∧ 7 ∣ n ∧ 8 ∣ n ∧ 9 ∣ n).card = 179 := by
  native_decide