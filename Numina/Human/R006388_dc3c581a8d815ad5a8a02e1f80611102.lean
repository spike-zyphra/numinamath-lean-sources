import Mathlib
/- Let $M \ge 4$ be an integer. Consider an $M$-digit natural number $n$, denoted by $d_{M-1}d_{M-2}...d_1d_0$, where $d_{M-1}$ is the most significant digit and $d_0$ is the least significant digit. The number $n$ must satisfy the following properties:
1. The digit $d_{M-2}$ is equal to the sum of $d_0$ and nine times $d_{M-1}$. (i.e., $d_{M-2} = 9 d_{M-1} + d_0$).
2. The sum of the digits $d_{M-1}$ and $d_{M-2}$ is less than twice the digit $d_1$. (i.e., $d_{M-1} + d_{M-2} < 2 d_1$).
3. The digit $d_1$ (the tens digit) is prime. All other digits $d_k$ for $k \in \{0, 2, 3, \dots, M-3, M-2, M-1\}$ are not prime. Specifically, the digits $d_k$ for $2 \le k \le M-3$ (if any such $k$ exist) must be $0$.

Show that the unique such number $n$ is $1 \cdot 10^{M-1} + 9 \cdot 10^{M-2} + 7 \cdot 10^1$.
(This number can be written as $190...070$, where there are $M-4$ zeros between the digit 9 and the digit 7). -/
theorem number_theory_636553 (m : ℕ) (hm : m ≥ 4) (d : ℕ → ℕ) (h : ∀ i : ℕ, i < m → d i < 10) (h1 : d (m - 2) = 9 * d (m - 1) + d 0) (h2 : d (m - 1) + d (m - 2) < 2 * d 1) (h3 : Nat.Prime (d 1)) (h4 : ∀ i : ℕ, i ≥ 2 ∧ i ≤ m - 1 → d i = 0) (h5 : d (m - 1) ≠ 0) : (∑ i in Finset.range m, d i * 10 ^ i) = 10 ^ (m - 1) + 9 * 10 ^ (m - 2) + 7 * 10 ^ 1:= by
  -- First, prove that d₀ = 0, d_{M-1} = 1, and d_{M-2} = 9
  have h6 : d 0 = 0 ∧ d (m - 1) = 1 ∧ d (m - 2) = 9:= by
    -- Use the constraint that d_{M-2} < 10 to derive the values
    have g1:= h (m - 2) (by omega)
    omega
  rcases h6 with ⟨h6, h7, h8⟩
  -- Next, prove that d₁ = 7 (the only prime digit that satisfies the inequality)
  have h9 : d 1 = 7:= by
    -- From the inequality, d₁ must be greater than 5
    replace h2 : d 1 > 5:= by omega
    -- Since d₁ is prime and greater than 5, it must be odd
    have g : Odd (d 1):= by
      -- d₁ cannot be 2 since it's greater than 5
      have g : d 1 ≠ 2:= by omega
      exact Nat.Prime.odd_of_ne_two h3 g
    rcases g with ⟨k, hk⟩
    -- Since d₁ < 10 and d₁ > 5, k can only be 3 or 4
    have hk1 : k = 3 ∨ k = 4:= by
      specialize h 1 (by omega)
      omega
    rcases hk1 with hk1 | hk1
    .
      -- Case k = 3: d₁ = 2*3 + 1 = 7, which is prime
      subst k
      rw [hk]
      simp
    .
      -- Case k = 4: d₁ = 2*4 + 1 = 9, which is not prime (contradiction)
      subst k
      simp at hk
      absurd h3
      rw [hk]
      decide
  -- Define the target number for comparison
  set a:= 10 ^ (m - 1) + 9 * 10 ^ (m - 2) + 7 * 10 ^ 1 with ha
  clear_value a
  -- Rewrite the sum to separate the first two terms
  rw [show m = m - 2 + 2 by omega]
  rw [Finset.sum_range_succ]
  rw [Finset.sum_range_succ]
  rw [show m - 2 + 1 = m - 1 by omega]
  rw [h7, h8]
  simp at ha ⊢
  -- General lemma: sum of digits can be rewritten as sum of middle digits plus first two digits
  have h10 : ∀ n : ℕ, ∑ x ∈ Finset.range (n + 2), d x * 10 ^ x = ∑ x ∈ Finset.range n, d (x + 2) * 10 ^ (x + 2) + d 1 * 10 + d 0:= by
    intro n
    induction n with
    | zero =>
      -- Base case: n = 0
      simp [Finset.sum_range_succ]
      ring_nf
    | succ n ih =>
      -- Inductive step: n + 1
      rw [show n + 1 + 2 = n + 2 + 1 by omega]
      rw [Finset.sum_range_succ]
      rw [ih]
      rw [Finset.sum_range_succ]
      linarith
  -- Apply the lemma with n = m - 4
  specialize h10 (m - 4)
  rw [show m - 4 + 2 = m - 2 by omega] at h10
  -- Prove that the sum of middle digits (d₂ to d_{M-3}) is zero
  have h11 : ∀ n : ℕ, n ≤ m - 4 → ∑ x ∈ Finset.range n, d (x + 2) * 10 ^ (x + 2) = 0:= by
    intro n hn
    induction n with
    | zero =>
      -- Base case: empty sum is zero
      simp
    | succ n ih =>
      -- Inductive step: add d_{n+2} * 10^{n+2} to the sum
      rw [Finset.sum_range_succ, ih (by omega)]
      -- But d_{n+2} = 0 by hypothesis h4
      specialize h4 (n + 2) (by omega)
      rw [h4]
      simp
  -- Apply the lemma to show middle digits sum to zero
  specialize h11 (m - 4) (by omega)
  -- Combine all results to prove the theorem
  rw [h10, h11, h6, h9, ha]
  simp
  ring_nf
