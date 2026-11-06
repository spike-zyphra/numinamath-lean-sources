import Mathlib

open Finset

def double_factorial (n : ℕ) := ∏ i ∈ Icc 2 n, if Even i then i else 1

theorem number_theory_94301 : (∑ i ∈ range 1011, double_factorial (2 * i + 2)) % 10 = 2 := by 
  native_decide