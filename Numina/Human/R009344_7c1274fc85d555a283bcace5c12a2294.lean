import Mathlib

/-Find the root(s) of the equation $\((x-2)(x-3)=x-2\)$.-/
theorem algebra_8978 (x : ℝ) : (x - 2) * (x - 3) = x - 2 ↔ x = 4 ∨ x = 2 := by
  constructor <;> intro h
  · -- First, we rewrite the equation as follows:
    -- \begin{align*}
    -- &(x-2)(x-3)-(x-2)=0 \\
    -- \Rightarrow &(x-2)(x-3)-1\cdot(x-2)=0 \\
    -- \Rightarrow &(x-2)\bigl((x-3)-1\bigr)=0 \\
    -- \Rightarrow &(x-2)(x-4)=0
    -- \end{align*}
    nth_rw 2 [←mul_one (x - 2)] at h
    -- Now, we have two possible cases:
    -- 1. $x-2=0$
    -- 2. $x-4=0$
    -- Solving each case separately:
    -- 1. $x-2=0$ implies $x=\boxed{2}$.
    -- 2. $x-4=0$ implies $x=\boxed{4}$.
    rcases (mul_eq_mul_left_iff.1 h) with h | h
    · left; linarith
    · right; linarith
  · -- Verify that $x=2$ or $x=4$ are the roots of $(x - 2) * (x - 3) = x - 2 $.
    rcases h with h | h <;> simp [h]; ring_nf
