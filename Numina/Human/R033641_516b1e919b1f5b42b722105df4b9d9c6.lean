import Mathlib

/-
Given the power function $f(x)=(m^{2}-5m+7)x^{m-2}$, find the value of $m$ that makes it an odd function.
-/
theorem algebra_9057
    {f : ℝ → ℝ}
    {m : ℝ}
    (hfp : m ^ 2 - 5 * m + 7 = 1)
    (hf : f = fun x => (m ^ 2 - 5 * m + 7) * x ^ (m - 2)) :
    (∀ x, f (-x) = - f x ) ↔ m = 3 := by

  constructor
  . intro hodd

    -- Since $f(x)$ is a power function, we have $m^{2}-5m+7=1$. Solving this equation, we get $m=2$ or $m=3$.
    have : m = 2 ∨ m = 3 := by
      apply sub_eq_zero_of_eq at hfp
      rw [show m ^ 2 - 5 * m + 7 - 1 = (m - 2) * (m - 3) by ring] at hfp
      rcases mul_eq_zero.mp hfp
      . left; linarith
      . right; linarith
    rcases this with hm | hm

    -- When $m=2$, $f(x)=1$ ($x\neq 0$), which is not an odd function.
    . simp [hf, hm] at hodd
      norm_num at hodd

    -- When $m=3$, $f(x)=x$, which is an odd function.
    . simp [hm]

  . intro hm
    simp [hf, hm]
    norm_num
