import Mathlib

open Real Set
open scoped BigOperators

open Polynomial

/- Determine the maximum and minimum values of the function $f(x) = 3x - x^3$ on the interval $[2, 3]$.-/
theorem algebra_9017 (f : ℝ → ℝ) (hf : f = λ x => 3 * x - x ^ 3) :
    IsGreatest (image f (Icc 2 3)) (-2) ∧ IsLeast (image f (Icc 2 3)) (-18) := by
  -- Since f(x) is antitone on $[2, 3]$, it's easy to find its maximum and minimum value.
  -- We show that f(x) is antitone by calculating its deriv.
  have fanti : AntitoneOn f (Icc 2 3) := by
    let p : ℝ[X] := C 3 * X - X ^ 3
    have hpf : f = fun x => p.eval x := by ext x; simp [hf, p]
    have derivp : deriv (fun x => p.eval x) = fun x => 3 - 3 * x ^ 2 := by
      ext x
      rw [Polynomial.deriv]
      simp [p]
    apply antitoneOn_of_deriv_nonpos
    . exact convex_Icc 2 3
    . rw [hpf]
      exact Polynomial.continuousOn_aeval p
    . rw [hpf]
      exact Polynomial.differentiableOn_aeval p
    simp
    intro x hx1 hx2
    rw [hpf, derivp]
    simp
    rw [abs_of_pos (by positivity)]
    linarith
  constructor
  -- The minimum value of f(x) on $[2, 3]$ reached at x=2.
  . constructor
    . rw [hf]
      use 2
      norm_num
    simp [upperBounds]
    intro a x hx1 hx2 hfx
    rw [show -2 = f 2 by norm_num [hf], ← hfx]
    apply fanti
    . norm_num
    . exact ⟨hx1, hx2⟩
    . exact hx1
  -- The maximum value of f(x) on $[2, 3]$ reached at x=3.
  constructor
  . rw [hf]
    use 3
    norm_num
  simp [lowerBounds]
  intro a x hx1 hx2 hfx
  rw [show -18 = f 3 by norm_num [hf], ← hfx]
  apply fanti
  . exact ⟨hx1, hx2⟩
  . norm_num
  . exact hx2
