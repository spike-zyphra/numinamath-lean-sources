import Mathlib
/- Denote $\mathbb{Z}_ {>0}=\{1,2,3, \ldots\}$ the set of all positive integers. Determine all functions $f: \mathbb{Z}_ {>0} \rightarrow \mathbb{Z}_{>0}$ such that, for each positive integer $n$,
i) $\sum_{k=1}^{n} f(k)$ is a perfect square, and
ii) $f(n)$ divides $n^{3}$. -/
theorem number_theory_604700 (f : ℕ → ℕ) : ((∀ n : ℕ, f n > 0) ∧ (∀ n : ℕ, ∃ m : ℕ, m ^ 2 = ∑ i in Finset.range n, f i) ∧ (∀ n : ℕ, f n ∣ (n + 1) ^ 3)) ↔ ∀ n : ℕ, f n = (n + 1) ^ 3:= by
  constructor
  -- Forward direction: if f satisfies the conditions, then f(n) = (n+1)³
  .
    intro h
    rcases h with ⟨h1, h2, h3⟩
    -- Prove by strong induction that f(n) = (n+1)³ for all n ≤ k
    have h4 : ∀ k : ℕ, ∀ n : ℕ, n ≤ k → f n = (n + 1) ^ 3:= by
      intro k
      induction k with
      | zero =>
        -- Base case: n = 0
        intro n hn
        simp at hn
        subst n
        simp
        -- f(0) must divide 1³ = 1, so f(0) = 1 = (0+1)³
        specialize h3 0
        simp at h3
        exact h3
      | succ k ih =>
        -- Inductive step: assume true for all n ≤ k, prove for n ≤ k+1
        intro n hn
        by_cases hn1 : n ≤ k
        .
          -- If n ≤ k, use inductive hypothesis
          exact ih n hn1
        .
          -- If n = k+1, prove f(k+1) = (k+2)³
          replace hn : n = k + 1:= by omega
          clear hn1
          subst n
          -- Use the perfect square condition for sum up to k+2
          have h4:= h2 (k + 1 + 1)
          rcases h4 with ⟨m, hm⟩
          set t:= k + 1 with ht
          clear_value t
          -- By inductive hypothesis, sum up to t equals sum of (i+1)³
          have h4 : ∑ i ∈ Finset.range t, f i = ∑ i ∈ Finset.range t, (i + 1) ^ 3:= by
            have h4 : ∀ i : ℕ, i ∈ Finset.range t → f i = (i + 1) ^ 3:= by
              intro i hi
              simp at hi
              subst t
              exact ih i (by omega)
            exact Finset.sum_congr rfl h4
          -- Known formula: 4 * ∑(i+1)³ = n²(n+1)²
          have h5 : ∀ n : ℕ, 4 * ∑ i ∈ Finset.range n, (i + 1) ^ 3 = n ^ 2 * (n + 1) ^ 2:= by
            intro n
            induction n with
            | zero =>
              simp
            | succ n ih =>
              rw [Finset.sum_range_succ]
              linarith
          rw [Finset.sum_range_succ] at hm
          -- Apply the formula to get the sum up to t
          have h6 : 4 * ∑ x ∈ Finset.range t, f x = t ^ 2 * (t + 1) ^ 2:= by rw [h4, h5 t]
          -- f(t) must divide (t+1)³
          specialize h3 t
          have g1 : (t + 1) ^ 3 > 0:= by positivity
          replace g1 : f t ≤ (t + 1) ^ 3:= by exact Nat.le_of_dvd g1 h3
          -- Prove by contradiction that f(t) = (t+1)³
          by_contra H
          replace H : f t < (t + 1) ^ 3:= by omega
          clear g1
          clear h4 h5
          -- Show that 2 divides t(t+1) (consecutive integers)
          have g1 : 2 ∣ t * (t + 1):= by
            by_cases g1 : Odd t
            .
              have g : Odd 1:= by decide
              replace g1 : Even (t + 1):= by exact Odd.add_odd g1 g
              replace g1 : 2 ∣ t + 1:= by exact even_iff_two_dvd.mp g1
              exact Dvd.dvd.mul_left g1 t
            .
              simp at g1
              replace g1 : 2 ∣ t:= by exact even_iff_two_dvd.mp g1
              exact Dvd.dvd.mul_right g1 (t + 1)
          rcases g1 with ⟨u, hu⟩
          -- Rewrite using the factorization
          rw [show t ^ 2 * (t + 1) ^ 2 = (2 * u) ^ 2 by rw [←hu] ; ring_nf] at h6
          replace h6 : ∑ x ∈ Finset.range t, f x = u ^ 2:= by linarith
          rw [h6] at hm
          -- Since f(t) > 0, we have m > u
          have h4 : m > u:= by
            by_contra H
            simp at H
            replace H : m ^ 2 ≤ u ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
            specialize h1 t
            linarith
          -- Set l = m - u and derive contradiction
          set l:= m - u with hl
          clear_value l
          replace hl : m = l + u:= by omega
          subst m
          simp at h4
          replace hm : f t = l * (l + 2 * u):= by linarith
          rw [←hu] at hm
          rw [hm] at H
          -- Show l < t+1
          replace H : (t + 1) * ((t + 1) ^ 2 + l) > l * ((t + 1) ^ 2 + l):= by linarith
          have g1 : (t + 1) ^ 2 + l > 0:= by positivity
          replace H : t + 1 > l:= by exact (Nat.mul_lt_mul_right g1).mp H
          -- f(t) = l(l + 2u) must divide (t+1)³
          replace g1 : l + t * (t + 1) ∣ (t + 1) ^ 3:= by
            rw [hm] at h3
            exact dvd_of_mul_left_dvd h3
          rcases g1 with ⟨s, hs⟩
          -- Show s > t+1
          have hs1 : s > t + 1:= by
            replace H : l + t * (t + 1) < (t + 1) ^ 2:= by linarith
            have hspos : s > 0:= by
              by_contra H
              simp at H
              subst s
              simp at hs
            replace H : (l + t * (t + 1)) * s < (t + 1) ^ 2 * s:= by exact Nat.mul_lt_mul_of_pos_right H hspos
            rw [←hs] at H
            rw [show (t + 1) ^ 3 = (t + 1) ^ 2 * (t + 1) by ring_nf] at H
            have g1 : (t + 1) ^ 2 > 0:= by positivity
            exact (Nat.mul_lt_mul_left g1).mp H
          -- Show s < t+2, leading to contradiction
          have hs2 : s < t + 2:= by
            by_contra H
            simp at H
            have g1 : l + t * (t + 1) ≥ 1 + t * (t + 1):= by omega
            replace g1 : (l + t * (t + 1)) * s ≥ (1 + t * (t + 1)) * s:= by exact Nat.mul_le_mul_right s g1
            have g2 : (1 + t * (t + 1)) * s ≥ (1 + t * (t + 1)) * (t + 2):= by exact Nat.mul_le_mul_left (1 + t * (t + 1)) hs1
            linarith
          linarith
    -- Apply the strong induction result
    intro n
    exact h4 n n (by omega)
  -- Backward direction: if f(n) = (n+1)³, then f satisfies the conditions
  .
    intro h
    refine ⟨?_, ?_, ?_⟩
    -- Condition 1: f(n) > 0 for all n
    .
      intro n
      rw [h n]
      positivity
    -- Condition 2: sum is a perfect square
    .
      intro n
      -- Use the known formula for sum of cubes
      have h1 : ∀ n : ℕ, 4 * ∑ i ∈ Finset.range n, (i + 1) ^ 3 = n ^ 2 * (n + 1) ^ 2:= by
        intro n
        induction n with
        | zero =>
          simp
        | succ n ih =>
          rw [Finset.sum_range_succ]
          linarith
      specialize h1 n
      -- Show that 2 divides n(n+1)
      have h2 : 2 ∣ n * (n + 1):= by
        by_cases h2 : Odd n
        .
          have g : Odd 1:= by decide
          replace h2 : Even (n + 1):= by exact Odd.add_odd h2 g
          replace h2 : 2 ∣ n + 1:= by exact even_iff_two_dvd.mp h2
          exact Dvd.dvd.mul_left h2 n
        .
          simp at h2
          replace h2 : 2 ∣ n:= by exact even_iff_two_dvd.mp h2
          exact Dvd.dvd.mul_right h2 (n + 1)
      rcases h2 with ⟨u, hu⟩
      -- Show the sum equals u²
      rw [show n ^ 2 * (n + 1) ^ 2 = (2 * u) ^ 2 by rw [←hu] ; ring_nf] at h1
      replace h1 : ∑ i ∈ Finset.range n, (i + 1) ^ 3 = u ^ 2:= by linarith
      use u
      rw [←h1]
      exact Eq.symm (Finset.sum_congr rfl fun x _ => h x)
    -- Condition 3: f(n) divides (n+1)³
    .
      intro n
      rw [h n]
