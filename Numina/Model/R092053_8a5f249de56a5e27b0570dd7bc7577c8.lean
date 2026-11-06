import Mathlib

open Finset

theorem number_theory_5288 {n : ℕ} (hn : n = 20480) :
  ∑ d ∈ n.divisors, (1 : ℚ)/d = 2 + 4093/10240 := by 
  rw [hn]
  native_decide