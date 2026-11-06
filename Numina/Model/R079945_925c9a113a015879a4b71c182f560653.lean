import Mathlib

theorem number_theory_290823 : 2011 ∣ (∏ i in Finset.range 1005, (2 * i + 1)) + (∏ i in Finset.range 1005, (2 * i + 2)) := by
  native_decide