import Mathlib

/-Add $4_6 + 14_6.$ Express your answer in base $6.$

The final answer is $ \boxed{22_6} $-/
theorem number_theory_16048 : Nat.ofDigits 6 [4] + Nat.ofDigits 6 [4, 1] = Nat.ofDigits 6 [2, 2] := by
  -- $4_6$ is 4 and $14_6$ is 10, so $4_6 + 14_6 = 14$, i.e. $22_6$.
  simp [Nat.ofDigits]
