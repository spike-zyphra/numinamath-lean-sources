import Mathlib
/- Let $N \ge 2$ be an integer representing the number of baskets. There are three types of fruits: apples, peaches, and pears. Let $a_k, e_k, p_k$ denote the number of apples, peaches, and pears in basket $k$ (for $k \in \{0, \dots, N-1\}$), respectively. These are non-negative integers.
The relations are:
1. For each basket $k$, the number of peaches $e_k$ is equal to the sum of apples $a_j$ in all other baskets $j \ne k$.
2. For each basket $k$, the number of apples $a_k$ is equal to the sum of pears $p_j$ in all other baskets $j \ne k$.
3. For each basket $k$, the number of pears $p_k$ is equal to the sum of peaches $e_j$ in all other baskets $j \ne k$.
Show that the total number of fruits, $S = \sum_{k=0}^{N-1} (a_k+e_k+p_k)$, is a multiple of $N^2-N+1$. -/
theorem number_theory_641231 (a e p : ℕ → ℕ) (A E P n : ℕ) (hn : n ≥ 2) (hA : A = ∑ i in Finset.range n, a i) (hE : E = ∑ i in Finset.range n, e i) (hP : P = ∑ i in Finset.range n, p i) (h1 : ∀ k ∈ Finset.range n, e k = A - a k) (h2 : ∀ k ∈ Finset.range n, a k = P - p k) (h3 : ∀ k ∈ Finset.range n, p k = E - e k) : n ^ 2 - n + 1 ∣ A + E + P:= by
  -- Prove that each sum is greater than or equal to any individual term
  have g1 : ∀ k ∈ Finset.range n, A ≥ a k:= by
    intro k hk
    subst A
    exact CanonicallyOrderedAddCommMonoid.single_le_sum hk
  have g2 : ∀ k ∈ Finset.range n, E ≥ e k:= by
    intro k hk
    subst E
    exact CanonicallyOrderedAddCommMonoid.single_le_sum hk
  have g3 : ∀ k ∈ Finset.range n, P ≥ p k:= by
    intro k hk
    subst P
    exact CanonicallyOrderedAddCommMonoid.single_le_sum hk

  -- Rewrite the relations to show that each fruit type plus its corresponding count equals the total
  replace h1 : ∀ k ∈ Finset.range n, e k + a k = A:= by
    intro k hk
    replace h1:= h1 k hk
    replace g1:= g1 k hk
    omega
  replace h2 : ∀ k ∈ Finset.range n, a k + p k = P:= by
    intro k hk
    replace h2:= h2 k hk
    replace g3:= g3 k hk
    omega
  replace h3 : ∀ k ∈ Finset.range n, p k + e k = E:= by
    intro k hk
    replace h3:= h3 k hk
    replace g2:= g2 k hk
    omega
  clear g1 g2 g3

  -- Show that all baskets have the same number of apples
  have h4 : ∀ k ∈ Finset.range n, a k = a 0:= by
    intro k hk
    have h4:= h1 0 (by simp ; omega)
    have h5:= h2 0 (by simp ; omega)
    have h6:= h3 0 (by simp ; omega)
    replace h1:= h1 k hk
    replace h2:= h2 k hk
    replace h3:= h3 k hk
    linarith

  -- Show that all baskets have the same number of pears
  have h5 : ∀ k ∈ Finset.range n, p k = p 0:= by
    intro k hk
    have h4:= h1 0 (by simp ; omega)
    have h5:= h2 0 (by simp ; omega)
    have h6:= h3 0 (by simp ; omega)
    replace h1:= h1 k hk
    replace h2:= h2 k hk
    replace h3:= h3 k hk
    linarith

  -- Show that all baskets have the same number of peaches
  have h6 : ∀ k ∈ Finset.range n, e k = e 0:= by
    intro k hk
    have h4:= h1 0 (by simp ; omega)
    have h5:= h2 0 (by simp ; omega)
    have h6:= h3 0 (by simp ; omega)
    replace h1:= h1 k hk
    replace h2:= h2 k hk
    replace h3:= h3 k hk
    linarith

  -- Rewrite the sums using the fact that all baskets have identical contents
  replace hA : A = ∑ _ ∈ Finset.range n, a 0:= by
    subst A
    exact Finset.sum_congr rfl h4
  replace hE : E = ∑ _ ∈ Finset.range n, e 0:= by
    subst E
    exact Finset.sum_congr rfl h6
  replace hP : P = ∑ _ ∈ Finset.range n, p 0:= by
    subst P
    exact Finset.sum_congr rfl h5

  -- Simplify the sums to get A = n * a_0, E = n * e_0, P = n * p_0
  simp at hA hE hP
  replace h1:= h1 0 (by simp ; omega)
  replace h2:= h2 0 (by simp ; omega)
  replace h3:= h3 0 (by simp ; omega)

  -- Set m = n - 2 to simplify the algebra
  set m:= n - 2 with hm
  clear_value m
  replace hm : n = m + 2:= by omega
  subst n

  -- Expand the expression and simplify
  ring_nf
  rw [show 1 + (4 + m * 4 + m ^ 2 - (2 + m)) = 3 + 3 * m + m ^ 2 by omega]
  subst A E P

  -- Use the relations to express everything in terms of a_0
  replace hA : e 0 = (m + 1) * a 0:= by linarith
  replace hE : p 0 = (m + 1) * e 0:= by linarith
  replace hP : a 0 = (m + 1) * p 0:= by linarith
  rw [hE, hA] at hP ⊢

  -- Case analysis: when m = 0 (i.e., n = 2)
  by_cases hm : m = 0
  .
    subst m
    simp
    use a 0 + a 0
    ring
  .
    -- When m > 0, derive a contradiction unless a_0 = 0
    replace hP : (m + 1) ^ 3 * a 0 = a 0:= by linarith
    have h : a 0 = 0:= by
      by_contra H
      replace hP : (m + 1) ^ 3 = 1:= by exact (Nat.mul_eq_right H).mp hP
      have g : m + 1 ≥ 2:= by omega
      replace g : (m + 1) ^ 3 ≥ 2 ^ 3:= by exact Nat.pow_le_pow_of_le_left g 3
      linarith
    rw [h]
    simp
