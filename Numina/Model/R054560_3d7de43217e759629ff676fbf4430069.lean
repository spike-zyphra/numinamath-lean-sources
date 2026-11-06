import Mathlib

theorem number_theory_192879 :
    (∑ x in (Finset.Ioc (-154) 145 : Set ℤ), x) < (∏ x in (Finset.Ico (-149) 88 : Set ℤ), x) ∧
    (∏ x in (Finset.Ico (-149) 88 : Set ℤ), x) - (∑ x in (Finset.Ioc (-154) 145 : Set ℤ), x) = 1196 := by
  native_decide