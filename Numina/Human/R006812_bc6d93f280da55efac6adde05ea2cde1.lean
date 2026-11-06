import Mathlib
set_option linter.unusedVariables false

/-
Theorem Number_Theory_641407: Proves an inequality involving natural numbers, divisors, and greatest common divisors
-/
theorem Number_Theory_641407 
    (V k1 k2 Cm Vdivk1 Vdivk2 k1divV k2divV n0 : ℕ)
    (hpos : 0 < V ∧ 0 < k1 ∧ 0 < k2 ∧ 0 < Cm)

  -- k1 and k2 are divisors of V
  (hdiv : k1 ∣ V ∧ k2 ∣ V)

  -- n0 is defined as the greatest common divisor of (V/k1) and (V/k2
  (hn0 : n0 = Nat.gcd (V / k1) (V / k2))
  (hdiv1 : k1 ∣ n0 )
  (hdiv2 : k2 ∣ n0) :
  n0 ≤ Cm * n0 := by 
  have t0 : (Cm : ℕ) ≥ 1 :=by linarith

   -- Using the lemma that n ≤ Cm*n when Cm ≥ 1
  have t1 : n0 ≤ Cm * n0:= by exact Nat.le_mul_of_pos_left n0 t0 
  exact t1 