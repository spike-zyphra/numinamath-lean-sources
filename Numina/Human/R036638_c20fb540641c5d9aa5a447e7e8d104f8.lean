import Mathlib
open Real
/- 8-26 Given the sequence $\left\{a_{n}\right\}$ satisfies
$$a_{1}=\frac{1}{2}, a_{1}+a_{2}+\cdots+a_{n}=n^{2} a_{n}, n \geqslant 1 .$$

Find the general term formula for $a_{n}$. -/
theorem algebra_599145 {a : ℕ → ℝ} (ha1 : a 1 = 1 / 2) (han : ∀ n ≥ 1, ∑ i in Finset.Icc 1 n, a i = n ^ 2 * a n) :
∀ n, n ≥ 1 → a n = 1 / (n * (n + 1)):= by
  -- Rewrite the recurrence relation to express a_(n+1) in terms of a_n
  replace han : ∀ n ≥ 1, a (n + 1) = (n + 1) ^ 2 * a (n + 1) - n ^ 2 * a n:= by
    intro n hn
    -- Apply the original condition to n+1
    have h1:= han (n + 1) (by linarith)
    -- Apply the original condition to n
    have h2:= han n (by linarith)
    -- Use the property of sum over Icc with successive upper bounds
    rw [Finset.sum_Icc_succ_top, h2] at h1
    clear h2
    simp at h1
    linarith
    linarith
  intro n hn
  -- Prove by induction on n
  induction n, hn using Nat.le_induction with
  | base =>
    -- Base case: n = 1
    rw [ha1]
    norm_num
  | succ n hn ih =>
    -- Inductive step: assume formula holds for n, prove for n+1
    specialize han n (by linarith)
    -- Substitute the induction hypothesis
    rw [ih] at han
    simp
    field_simp
    -- Simplify algebraic expressions
    rw [show (↑n : ℝ) + 1 + 1 = n + 2 by ring_nf]
    rw [show (↑n : ℝ) ^ 2 * (1 / (↑n * (↑n + 1))) = ↑n / (↑n + 1) by field_simp ; linarith] at han
    -- Rearrange to isolate a_(n+1)
    replace han : n * (n + 2) * a (n + 1) = n / (n + 1):= by linarith
    replace han : a (n + 1) = n / (n + 1) / (n * (n + 2)):= by
      rw [←han]
      field_simp
    -- Apply the derived formula for a_(n+1)
    rw [han]
    -- Simplify to match the target formula
    field_simp
    linarith
