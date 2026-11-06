import Mathlib

/-Let the function $f(x)$ be an even function defined on $\mathbb{R}$, such that for any $x \in \mathbb{R}$, $f(x+6) = f(x) + f(3)$, and $f(2) = 3$. Find the value of $f(2006) + f(2007)$.-/
theorem algebra_9162 {f : ℝ → ℝ} (h0 : ∀ x, f (-x) = f x)
(h1 : ∀ x, f (x + 6) = f x + f 3) (h2 : f 2 = 3) :
f 2006 + f 2007 = 3 := by
-- Prove that $f(3)$ equals $0$
  have h3 : f 3 = 0 := by
    have r1 := h1 (-3)
    rw [show -(3:ℝ)+6=3 by norm_num] at r1; simp at r1
    have r2 := h0 (-3)
    simp at r2; linarith
    

-- Prove that $f$ is periodic and its period is $6$
  have perf : ∀ x, f (x + 6) = f x := by
    intro x; rw [h1]; simp; assumption

-- In particular, $f$ takes a same value at numbers whose differences are multiple of $6$
  have mul6 : ∀ x (n : ℕ), f x = f (x + 6 * n) := by
    intro x n; induction n with
    | zero => simp
    | succ n ih =>
      push_cast; rw [mul_add, mul_one, ← add_assoc]; rw [perf]; assumption

-- Compute $f(2006)$ and $f(2007)$
  rw [show (2006:ℝ)=2+6*(334:ℕ) by norm_num, ← mul6]
  rw [show (2007:ℝ)=3+6*(334:ℕ) by norm_num, ← mul6]
  rw [h2, h3]; norm_num