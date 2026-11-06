import Mathlib
set_option maxRecDepth 1000

open Finset

theorem number_theory_611062 : #{P ∈ (Icc 1 60) ×ˢ (Icc 1 60) | P.1 ≤ P.2 ∧
    P.1 ∣ P.2 ∧ P.1 + 1 ∣ P.2 + 1} = 106 := by 
  native_decide