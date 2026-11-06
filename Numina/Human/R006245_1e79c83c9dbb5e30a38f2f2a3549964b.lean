import Mathlib
/- Let $K$ be an integer greater than or equal to 2. Let $n = 2^K - 1$.
Show that the sum $\sum_{i=0}^{n-1} (\text{if } \operatorname{Odd}(i) \text{ then } (i+1) \text{ else } (2^i)(i+1))$ is equal to $2^{K-2}(2^K-(K+1))$. -/
theorem number_theory_635116 (k n : ℕ) (hk : k ≥ 2) (hn : n = 2 ^ k - 1) : ∑ i in Finset.range n, (if Odd i then (i : ℤ) + 1 else (2 : ℤ) ^ i * (i + 1)) = ((3 * 2 ^ k - 5) * 2 ^ (2 ^ k) + 5) / 9 + 2 ^ (2 * k - 2) - 2 ^ (k - 1):= by
  -- Set m = k - 2 and clear its value for later use
  set m:= k - 2 with hm
  clear_value m
  -- Replace k with m + 2 using the relationship
  replace hm : k = m + 2:= by omega
  subst k
  clear hk
  -- Key lemma: Sum formula for range (2*t + 1) with conditional terms
  have h1 : ∀ t : ℕ, ∑ i in Finset.range (2 * t + 1), (if Odd i then (i : ℤ) + 1 else (2 : ℤ) ^ i * (i + 1)) = ∑ i in Finset.range t, (2 * i + 2) + ∑ i in Finset.range (t + 1), (2 : ℤ) ^ (2 * i) * (2 * i + 1):= by
    intro t
    -- Proof by induction on t
    induction t with
    | zero =>
      simp
    | succ t ih =>
      simp at ih
      simp
      -- Rewrite the range expression
      rw [show 2 * (t + 1) + 1 = 2 * t + 1 + 1 + 1 by omega]
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      rw [ih]
      -- Calculate sum of even terms (2*x + 2)
      have g1 : ∑ x ∈ Finset.range (t + 1), (2 * (↑x : ℤ) + 2) = ∑ x ∈ Finset.range t, (2 * (↑x : ℤ) + 2) + (2 * t + 2):= by rw [Finset.sum_range_succ]
      -- Calculate sum of odd terms (2^(2*x) * (2*x + 1))
      have g2 : ∑ x ∈ Finset.range (t + 1 + 1), (2 : ℤ) ^ (2 * x) * (2 * ↑x + 1) = ∑ x ∈ Finset.range (t + 1), (2 : ℤ) ^ (2 * x) * (2 * ↑x + 1) + (2 : ℤ) ^ (2 * (t + 1)) * (2 * (↑(t + 1) : ℤ) + 1):= by rw [Finset.sum_range_succ]
      rw [g1, g2]
      apply sub_eq_zero.1
      simp
      -- Set temporary variables for cleaner calculation
      set a:= ∑ x ∈ Finset.range t, (2 * (↑x : ℤ) + 2)
      set b:= ∑ i ∈ Finset.range (t + 1), 2 ^ (2 * i) * (2 * (↑i : ℤ) + 1)
      clear_value a b
      ring_nf
      -- Prove that 2 + t*2 is not odd
      have g3 : ¬Odd (2 + t * 2):= by
        simp
        use t + 1
        ring
      simp [g3]
  simp at h1
  -- Lemma: Sum of arithmetic sequence (2*i + 2) from 0 to n-1
  have h2 : ∀ n : ℕ, ∑ i in Finset.range n, (2 * i + 2) = n * (n + 1):= by
    intro n
    -- Proof by induction on n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  -- Lemma: Sum of geometric sequence with linear term (2^(2*i) * (2*i + 1))
  have h3 : ∀ n : ℕ, 9 * ∑ i in Finset.range (n + 1), (2 ^ (2 * i) * (2 * (↑i : ℤ) + 1)) = (6 * n + 1) * 2 ^ (2 * n + 2) + 5:= by
    intro n
    -- Proof by induction on n
    induction n with
    | zero =>
      simp
    | succ n ih =>
    rw [Finset.sum_range_succ]
    -- Distribute the multiplication
    rw [show 9 * (∑ x ∈ Finset.range (n + 1), 2 ^ (2 * x) * (2 * (↑x : ℤ) + 1) + 2 ^ (2 * (n + 1)) * (2 * (↑(n + 1) : ℤ) + 1)) = 9 * (∑ x ∈ Finset.range (n + 1), 2 ^ (2 * x) * (2 * (↑x : ℤ) + 1)) + 9 * (2 ^ (2 * (n + 1)) * (2 * (↑(n + 1) : ℤ) + 1)) by ring]
    rw [ih]
    simp
    apply sub_eq_zero.1
    ring_nf
  -- Set a = 2^(m+1) - 1 for convenience
  set a:= 2 ^ (m + 1) - 1 with ha
  clear_value a
  -- Express n in terms of a: n = 2*a + 1
  have ha1 : n = 2 * a + 1:= by
    subst a n
    have g : 2 ^ (m + 1) > 0:= by positivity
    rw [show 2 ^ (m + 2) = 2 * 2 ^ (m + 1) by ring]
    omega
  -- Express 2^(m+2) in terms of a
  have ha2 : 2 ^ (m + 2) = 2 * a + 2:= by omega
  -- Simplify power expressions
  rw [show 2 * (m + 2) - 2 = (m + 1) * 2 by omega]
  rw [show m + 2 - 1 = m + 1 by omega]
  -- Apply the main lemma h1 with a
  rw [ha1, h1 a]
  rw [ha2]
  zify at ha2
  rw [ha2]
  -- Express 2^(m+1) in terms of a
  have ha3 : 2 ^ (m + 1) = a + 1:= by
    have g : 2 ^ (m + 1) > 0:= by positivity
    omega
  -- Rewrite power expression using power of power rule
  rw [show (2 : ℤ) ^ ((m + 1) * 2) = (2 ^ (m + 1)) ^ 2 by exact pow_mul 2 (m + 1) 2]
  zify at ha3
  rw [ha3]
  -- Apply arithmetic sum formula h2
  specialize h2 a
  zify at h2
  rw [h2]
  -- Apply geometric sum formula h3 and solve for the sum
  specialize h3 a
  replace h3 : ∑ i ∈ Finset.range (a + 1), (2 : ℤ) ^ (2 * i) * (2 * ↑i + 1) = ((6 * ↑a + 1) * 2 ^ (2 * a + 2) + 5) / 9:= by
    rw [←h3]
    simp
  rw [h3]
  -- Simplify the coefficient expression
  rw [show 3 * (2 * (↑a : ℤ) + 2) - 5 = 6 * a + 1 by ring]
  -- Final algebraic simplification
  ring_nf
