import Mathlib
open Finset
theorem number_theory_611222 :
  let positions := (((Icc 1 10).product (Icc 1 10)).filter (λ p => 10 * (p.1 - 1) + p.2 + 10 * (p.2 - 1) + p.1 = 101))
  positions.card = 10 := by
  intro positions
  native_decide