import Mathlib

/-
Given a function $f(x) =
\begin{cases}
x^2 + x, & \text{if } x \geq 0 \\
x - x^2, & \text{if } x < 0
\end{cases}$, if $f(a) > f(2-a)$, then the range of values for $a$ is ______.
-/
theorem algebra_9006 {f : ℝ → ℝ}
    (hf : ∀ x, 0 ≤ x → f x = x ^ 2 + x)
    (hf' : ∀ x, x < 0 → f x = x - x ^ 2) (a : ℝ) :
    f a  > f (2 - a) ↔ 1 < a := by

  -- $f(x)$ is strictly increasing
  have h_f_increasing : ∀ x y, x < y → f x < f y := by
    intro x y h_xlty
    apply sub_neg.mp
    rcases le_or_lt 0 x with hx | hx
    . rcases le_or_lt 0 y with hy | hy
      . rw [hf x hx, hf y hy]
        rw [show x ^ 2 + x - (y ^ 2 + y) = (x - y) * (x + y + 1) by ring]
        apply mul_neg_of_neg_of_pos
        <;> linarith
      . linarith
    . rcases le_or_lt 0 y with hy | hy
      . rw [hf' x hx, hf y hy]
        rw [show x - x ^ 2 - (y ^ 2 + y) = -(x ^ 2 + y ^ 2) + (x - y) by ring]
        apply Right.add_neg
        <;> linarith [sq_pos_of_neg hx, sq_nonneg y]

      . rw [hf' x hx, hf' y hy]
        rw [show x - x ^ 2 - (y - y ^ 2) = (y - x) * (y + x - 1) by ring]
        apply mul_neg_of_pos_of_neg
        <;> linarith
  -- $\all x y, f x < f y \rarr x < y
  have h_f_increasing' : ∀ x y, f x < f y → x < y := by
    intro x y hxy
    by_contra! h_contra
    rcases eq_or_ne x y with h | h
    . simp_all
    apply lt_of_le_of_ne at h_contra
    specialize h_contra h.symm
    specialize h_f_increasing y x h_contra
    linarith

  -- Now, solving for $a$, we get: $a > 2 - a$. Therefore, the range of values for $a$ is $a > 1$.
  constructor
  . intro h
    specialize h_f_increasing' (2 - a) a h
    linarith
  . intro h
    specialize h_f_increasing (2 - a) a (by linarith)
    linarith
