import Mathlib
/- Let $C$ be an even positive integer. Let $N$ be a positive integer such that $N$ is a multiple of $C/2$, the quotient $X = N/(C/2)$ is an odd integer, and $X \ge C+1$. Show that there exists a non-negative integer $k$ such that $N$ is the sum of the $C$ consecutive positive integers starting from $k+1$ (i.e., $N = (k+1) + (k+2) + \dots + (k+C)$). -/
theorem number_theory_639795 (c n : ℕ) (hc : c > 0) (h1 : Even c) (h2 : c / 2 ∣ n) (h3 : Odd (n / (c / 2))) (h4 : n / (c / 2) ≥ c + 1) : ∃ k : ℕ, n = ∑ i in Finset.range c, (k + 1 + i):= by
  -- Extract the value k from the Even hypothesis where c = 2k
  rcases h1 with ⟨k, rfl⟩
  -- Simplify c/2 to k using the fact that c = 2k
  rw [show (k + k) / 2 = k by refine Eq.symm (Nat.eq_div_of_mul_eq_right (by omega) (by omega))] at h2 h3 h4
  -- Extract t from the divisibility hypothesis
  rcases h2 with ⟨t, rfl⟩
  simp at hc
  -- Simplify the division by k
  rw [show k * t / k = t by exact Nat.mul_div_right t hc] at h3 h4
  -- Rewrite k + k as 2 * k
  rw [show k + k = 2 * k by ring] at h4 ⊢
  -- Extract t from the Odd hypothesis
  rcases h3 with ⟨t, rfl⟩
  -- Define s as t - k to help with the final calculation
  set s:= t - k with hs
  clear_value s
  -- Establish the relationship between t and s
  replace hs : t = s + k:= by omega
  subst t
  use s
  -- Helper lemma: Proves the sum formula for arithmetic sequence
  have h1 : ∀ n : ℕ, ∑ i ∈ Finset.range (2 * n), (s + 1 + i) = n * (2 * s + 2 * n + 1):= by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [show 2 * (n + 1)= 2 * n + 1 + 1 by omega]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      ring
  -- Apply the helper lemma and complete the proof
  rw [h1 k]
  ring
