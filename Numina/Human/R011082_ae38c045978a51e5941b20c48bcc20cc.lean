import Mathlib

/-If $C=\frac{5}{9}(F-32)$, what is $F$ when $C=20$?-/
theorem algebra_11204 (C F : ℝ) (hC : C = 5 / 9 * (F - 32)) (hC1 : C = 20) : F = 68 := by
-- This is a straightforward simplification: plug in $C=20$ to the equation and solve for $F$
  rw [hC1] at hC
  apply_fun (fun x => 9 / (5 : ℝ) * x + 32) at hC; ring_nf at hC
  symm; assumption