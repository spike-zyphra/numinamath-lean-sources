import Mathlib

open Add

/-
The displacement $s$ (in meters) of an object as a function of time $t$ (in seconds) is given by $s=4-2t+t^2$. Calculate the instantaneous velocity of the object at the end of 3 seconds.
-/
theorem algebra_9221 (s : ℝ → ℝ) (h₀ : s = fun t => 4 - 2 * t + t ^ 2) :
    deriv s 3 = 4 := by
  -- First, we unfold the definition of $s$
  rw [h₀]
  -- Now, we use the chain rule to calculate the derivative of $s$ with respect to $t$.
  rw [deriv_add,deriv_sub,deriv_const,deriv_const_mul,deriv_id'']
  -- All subgoals are easy to solve using the rules of algebra and calculus.
  simp_all; ring_nf; simp_all
  repeat
    simp
    apply DifferentiableAt.const_mul (by simp_all) 2
  simp
  -- Thus, we have $s'(3) = 4$.
