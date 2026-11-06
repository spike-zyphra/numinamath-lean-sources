import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_16053 {f : ℝ → ℝ} (hf : f = λ x => tan x + cot x) :
    Function.Periodic f (Real.pi) := by

  unfold Function.Periodic
  intro x
  rw [hf]
  -- We need to prove that $f(x + \pi) = f(x)$ i.e., $\tan(x + \pi) + \cot(x + \pi) = \tan x + \cot x$
  simp only
  -- Since `tan` and `cot` are both $\pi$-periodic, we can prove this equality.
  -- Let's establish that $\tan(x + \pi) = \tan(x)$
  have htan : tan (x + Real.pi) = tan x := by
    rw [tan_add_pi]
  -- Let's establish that $\cot(x + \pi) = \cot(x)$
  have hcot : cot (x + Real.pi) = cot x := by
    rw [cot_eq_cos_div_sin]
    rw [cot_eq_cos_div_sin]
    have hcosp : cos (x + Real.pi) = -cos x := by
      rw [cos_add_pi]
    have hsinp : sin (x + Real.pi) = -sin x := by
      rw [sin_add_pi]
    simp only [hcosp, hsinp]
    <;> ring

  -- Now combine both equalities to get $f(x + \pi) = f(x)$
  rw [htan, hcot]