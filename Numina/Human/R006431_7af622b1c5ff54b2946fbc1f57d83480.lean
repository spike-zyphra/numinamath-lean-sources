import Mathlib
/- Let $M$ be a non-negative integer. Define the function $f: \mathbb{N} \to \mathbb{N}$ by $f(k) = \sum_{i=0}^{k-1} \max(0, 3i-2)$ for $k \ge 0$. Show that there exists a natural number $n$ such that $f(n) \le M \le f(n+1)$.
Note: The sum $f(k)$ can also be expressed as $f(0)=0$, and $f(k)=\frac{(k-1)(3k-4)}{2}$ for $k \ge 1$. -/
theorem number_theory_636993 (m : ℕ) (f : ℕ → ℕ) (hf : f = fun k => ∑ i in Finset.range k, (3 * i - 2)) : ∃ n : ℕ, f n ≤ m ∧ m ≤ f (n + 1):= by

  -- Prove that f(0) = 0 using simplification
  have h1 : f 0 = 0:= by simp [hf]

  -- Key lemma: For any k, f(k+2) * 2 = (k+1) * (3k + 2)
  have h3 : ∀ k : ℕ, f (k + 2) * 2 = (k + 1) * (3 * k + 2):= by
    intro k
    induction k with
    | zero =>
      simp [hf, Finset.sum_range_succ]
    | succ k ih =>
      simp [hf] at ih ⊢
      rw [Finset.sum_range_succ]
      rw [show 3 * (k + 2) - 2 = 3 * k + 4 by omega]
      linarith

  -- Proof by contradiction
  by_contra H
  simp at H

  -- If the theorem is false, then f(n) ≤ m must hold for all n
  replace H : ∀ n : ℕ, f n ≤ m:= by
    intro n
    induction n with
    | zero =>
      simp [h1]
    | succ n ih =>
      replace H:= H n ih
      linarith

  -- Apply the key lemma with k = m
  specialize h3 m
  specialize H (m + 2)

  -- Derive a contradiction using arithmetic
  replace H : f (m + 2) * 2 ≤ m * 2:= by linarith
  rw [h3] at H
  ring_nf at H
  omega
