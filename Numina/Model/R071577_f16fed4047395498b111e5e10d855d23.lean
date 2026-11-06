import Mathlib

theorem number_theory_253448 : 1987 ∣ (∏ i ∈ Finset.range 993, (2 * i + 1)) + (∏ i ∈ Finset.range 993, (2 * i + 2)) := by
  native_decide