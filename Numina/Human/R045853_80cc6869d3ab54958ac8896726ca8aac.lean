import Mathlib

open Real

/- Let $f(x)=\frac{1}{x-3}$.  Find the largest $x$ that is not in the domain of $g(x)=f(f(x))$. -/
theorem algebra_21059 {f : ℝ → ℝ} (hf : f = fun x => 1 / (x - 3)) :
    IsGreatest {x | x = 3 ∨ f x = 3} (10 / 3) := by
  constructor
  -- $10/3$ is not in the domain of $g$ since $f(10/3) = 3$
  right
  rw [hf]
  ring
  -- $10/3$ is the greatest such value
  intro x xin
  simp only [hf, Set.mem_setOf_eq] at xin
  if hx : x = 3 then
    rw [hx]
    norm_num
  else
    simp only [hx, false_or] at xin
    have neq : x - 3 ≠ 0 := by
      by_contra contra
      apply eq_of_sub_eq_zero at contra
      contradiction
    field_simp at xin
    linarith