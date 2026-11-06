import Mathlib

open Real

/-Let $a\star b = \dfrac{\sqrt{a+b}}{\sqrt{a-b}}$. If $ x \star 24 = 7$, find $x$.

The final answer is $ \boxed{25} $-/
theorem algebra_10604 {x : ℝ} (hf : f = fun a b => sqrt (a + b) / sqrt (a - b)) (h : f x 24 = 7) :
  x = 25 := by
    -- We know that $x\star24=\dfrac{\sqrt{x+24}}{\sqrt{x-24}}=7$.
    simp [hf] at h
    --  Because we cannot take the square root of a negative number and because the denominator of a fraction cannot be zero, we know that $x-24>0$.
    have : 24 < x := by
      by_contra! xle24
      have : √(x - 24) = 0 := sqrt_eq_zero'.mpr (by linarith)
      simp [this] at h
    -- Rearrange the original equation, we get $x = 25$.
    rw [div_eq_iff (Real.sqrt_ne_zero'.2 (by linarith))] at h
    apply_fun (· ^ 2) at h
    rw [Real.sq_sqrt, mul_pow, Real.sq_sqrt] at h <;> linarith
