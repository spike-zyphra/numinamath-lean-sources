import Mathlib

theorem number_theory_251004 :
    ∑ n in (Finset.Ico 1 99), (if n / 9 < n % 9 then n else 0) = 960 := by 
  rfl