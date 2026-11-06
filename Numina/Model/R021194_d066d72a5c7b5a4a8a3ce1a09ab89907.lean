import Mathlib

theorem number_theory_288938 :
    ∑ N in (Finset.Ico 1 1000).filter (fun N => 257 ∣ N + 2^2015), N = 2054 := by
  native_decide