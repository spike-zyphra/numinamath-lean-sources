import Mathlib
open Nat Real Finset Set
set_option linter.unusedVariables false

theorem number_theory_600027 (n : ℕ) (h1 : 10 ≤ n) (h2 : n ≤ 99) (h3 : (10^n + 1) % 7 = 0) :
  
   (∑ n ∈ Finset.range 100 \ Finset.range 10, if (10^n + 1) % 7 = 0 then n else 0) = 855 := by

  native_decide