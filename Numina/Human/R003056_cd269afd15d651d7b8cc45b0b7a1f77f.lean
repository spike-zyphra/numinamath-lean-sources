import Mathlib
open Real

/- 7・21 Let $M=\{(x, y) \mid | x y | = 1, x > 0\}$,

$$

N=\{(x, y) \mid \operatorname{arctg} x + \operatorname{arcctg} y = \pi\},

$$


then
(A) $M \cup N=\{(x, y) \mid | x y | = 1\}$.
(B) $M \cup N=M$.
(C) $M \cup N=N$.
(D) $M \cup N=\{(x, y) \mid | x y | = 1$ and $x, y$ are not both negative $\}$. (China High School Mathematics League, 1982) -/
theorem algebra_149194
  (M N : Set (ℝ × ℝ)) (hM : M = {(x, y) | abs (x * y) = 1 ∧ x > 0})
  (hN : N = {(x, y) | arctan x + arctan y = π / 2}) :
  M ∪ N = M := by
  rw [hM, hN]
  ext x
  simp
  intro h
  -- show x * y = 1
  have h' : tan (arctan x.1) = tan (π / 2 - arctan x.2)
  · have : arctan x.1 = π / 2 - arctan x.2 := by linarith [h]
    rw [this]
  rw [Real.tan_pi_div_two_sub, tan_arctan, tan_arctan] at h'
  rw [abs_eq zero_le_one]
  constructor
  left
  rw [h']
  -- show x ≠ 0
  apply IsUnit.inv_mul_cancel
  rw [isUnit_iff_ne_zero]
  intro hz
  rw [hz, arctan_zero, add_zero] at h
  have := Real.arctan_lt_pi_div_two x.1
  linarith
  -- show x.1 > 0 by contradiction
  by_contra! hz1
  have ha1 : arctan x.1 ≤ 0
  · rw [←arctan_zero]
    exact Real.arctan_le_arctan hz1
  have ha2 : arctan x.2 ≤ 0
  · rw [←arctan_zero]
    apply arctan_le_arctan
    rw [←inv_nonpos, ←h']
    exact hz1
  linarith [pi_div_two_pos, ha1, ha2]