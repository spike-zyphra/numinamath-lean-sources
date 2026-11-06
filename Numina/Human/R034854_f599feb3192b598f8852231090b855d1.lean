import Mathlib

open Real Set
open scoped BigOperators

/- The function $\lfloor x\rfloor$ is defined as the largest integer less than or equal to $x$. For example, $\lfloor 5.67\rfloor = 5$, $\lfloor -\tfrac 14\rfloor = -1$, and $\lfloor 8\rfloor = 8$.

What is the range of the function $$f(x) = \lfloor x\rfloor - x~?$$Express your answer in interval notation. -/
theorem algebra_12605 : range (λ x => ⌊x⌋ - x) = {y | -1 < y ∧ y ≤ 0} :=
  ext fun x ↦ by
    constructor <;> simp (config := { contextual := true }) [Int.floor_le, Int.lt_floor_add_one]
    <;> intro h <;> omega