import Mathlib
/-
The function $f(x)$ satisfies

\[f(f(x)) = 6x - 2005\]for all real numbers $x.$  There exists an integer $n$ such that $f(n) = 6n - 2005.$  Find $n.$-/

theorem algebra_21774 {f : ℝ → ℝ} (h : ∀ x, f (f x) = 6 * x - 2005)
    (hn: f (n : ℤ ) = 6 * n - 2005)  : n = 401 := by
    --Setting $x = n,$ we get \[f(f(n)) = 6n - 2005,\]so $f(6n - 2005) = 6n - 2005.$  Then
    have heq := h (↑n)
    have heq2 : f ↑n = f (f ↑n) := by
      rw [← heq] at hn
      exact hn
    rw [hn] at heq
    have heq3 := h (6 * ↑n - 2005)
    --\[f(f(6n - 2005)) = f(6n - 2005) = 6n - 2005.\]But $f(f(6n - 2005)) = 6(6n - 2005) - 2005.$  Solving
    have heq4 : f (f (6 * ↑n - 2005)) =f (6 * ↑n - 2005) := by
      rw [heq]
      exact heq
    rw [heq3] at heq4
    rw [heq] at heq4
    --\[6(6n - 2005) - 2005 = 6n - 2005,\]we find $n = \boxed{401}.$
    ring_nf at heq4;
    have e := congrArg (fun (t) => (t - ↑n * (6 : ℝ) + 14035) / 30 ) heq4; beta_reduce at e; ring_nf at e
    norm_cast at e