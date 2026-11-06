import Mathlib

/-- Given that the function $f(x)$ is defined on $\mathbf{R}$
    and for all real numbers $x, y \in \mathbf{R}$,
    we have $f(x+y) + f(x-y) = 2 f(x) f(y)$, and $f(0) \neq 0$.
    (1) Prove that $f(0)=1$, and $f(x)$ is an even function;
    (2) If there exists a constant $c$ such that $f\left(\frac{c}{2}\right)=0$,
        (1) Prove that for any $x \in \mathbb{R}$, $f(x+c) = -f(x)$ holds;
        (2) Is the function $f(x)$ a periodic function? If so, find one of its periods. -/
theorem algebra_167736 {f : ℝ → ℝ} (h : ∀ x y, f (x + y) + f (x - y) = 2 * f x * f y)
    (h0 : f 0 ≠ 0) :
    f 0 = 1 ∧ (∀ y, f y = f (-y)) ∧ (∀ c, f (c / 2) = 0 → (∀ x, f (x + c) = -f x) ∧ f.Periodic (2 * c)) := by
  have f0 : f 0 = 1 := by
    -- Let $x = y = 0$, then $f(0) + f(0) = 2 f(0) f(0)$,
    specialize h 0 0
    norm_num at h
    -- hence $f(0) = f(0)^2$.
    have : f 0 ^ 2 = f 0 := by linarith
    -- Since $f(0) \ne 0$, we have $f(0) = 1$;
    have := eq_zero_or_one_of_sq_eq_self this
    tauto
  have feven : ∀ y, f y = f (-y) := by
    -- for any $y \in \mathbf R$, let $x = 0$, then $f(y) + f(-y) = 2f(0) f(y)$,
    intro y
    specialize h 0 y
    rw[f0] at h
    -- so $f(-y) = f(y)$, which means that the function $f$ is an even function.
    norm_num at h
    linarith
  split_ands
  · assumption
  · assumption
  · intro c czero
    have semiperiod : ∀ x, f (x + c) = -f x := by
      intro a
      -- Let $x = a + c/2, y = c/2$,
      specialize h (a + c/2) (c/2)
      rw[czero, add_assoc, add_halves] at h
      -- then $f(a+c) +f(a) = 0$,
      norm_num at h
      -- i.e., $f(x+c) = -f(x)$ holds.
      linarith
    constructor
    · assumption
    · intro x
      -- Since $f(x+2c) = -f(x+c)
      have sp1 := semiperiod (x + c)
      rw[add_assoc, ← two_mul] at sp1
      -- = f(x)$, the function $f$ is a periodic function with one of its period $T=2c$.
      rw[sp1, semiperiod x, neg_neg]