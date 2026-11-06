import Mathlib
open BigOperators

theorem number_theory_3786 {N : ℕ}
  (hN : N = ∑ i ∈ Finset.range 2023, 2023*10^(i*4)) : N % 13 = 8 := by 
  rw [hN]
  native_decide