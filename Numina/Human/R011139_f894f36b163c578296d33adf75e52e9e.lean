import Mathlib
set_option maxRecDepth 1000

open Finset

/-How many pairs of integers $(a, b)$, with $1 \leq a \leq b \leq 60$, have the property that $b$ is divisible by $a$ and $b+1$ is divisible by $a+1$ ?-/
theorem number_theory_611062 : #{P ∈ (Icc 1 60) ×ˢ (Icc 1 60) | P.1 ≤ P.2 ∧
    P.1 ∣ P.2 ∧ P.1 + 1 ∣ P.2 + 1} = 106 := by norm_cast