import Mathlib
/- Let the sequence ${{a}_ {n}}({{a}_ {n}} \geqslant 0)$ satisfy ${{a}_ {1}} = 0$, ${{a}_ {2}} = 1$, ${{a}_ {3}} = 9$, and $S_{n}^{2}{{S}_ {n-2}} = 10S_{n-1}^{3} (n > 3)$, where ${{S}_ {n}}$ is the sum of the first $n$ terms of the sequence ${{a}_ {n}}$. Find the expression for ${{a}_{n}} (n \geqslant 3)$. -/
theorem number_theory_630792 (a S : ℕ → ℝ) (hpos : ∀ n : ℕ, a n ≥ 0) (hS : ∀ n : ℕ, S n = ∑ i ∈ Finset.range n, a i) (h0 : a 0 = 0) (h1 : a 1 = 1) (h2 : a 2 = 9) (hn : ∀ n : ℕ, (S (n + 4)) ^ 2 * (S (n + 2)) = 10 * (S (n + 3)) ^ 3) : ∀ n : ℕ, n ≥ 2 → a n = 9 * 10 ^ (n - 2):= by
  -- First, prove that all partial sums S(n+2) are positive
  have hSpos : ∀ n : ℕ, S (n + 2) > 0:= by
    intro n
    induction n with
    | zero =>
      -- Base case: S(2) = a_0 + a_1 + a_2 = 0 + 1 + 9 = 10 > 0
      simp [hS, Finset.sum_range_succ, h0, h1, h2]
    | succ n hn' =>
      -- Inductive step: if S(n+2) > 0, then S(n+3) = S(n+2) + a(n+2) ≥ S(n+2) > 0
      rw [show n + 1 + 2 = n + 2 + 1 by ring]
      rw [hS (n + 2 + 1)]
      rw [Finset.sum_range_succ, ←hS (n + 2)]
      specialize hpos (n + 2)
      linarith
  -- Transform the recurrence relation to show S(n+3) = 10 * S(n+2)
  replace hn : ∀ n : ℕ, S (n + 3) = 10 * S (n + 2):= by
    intro n
    induction n with
    | zero =>
      -- Base case: verify S(3) = 10 * S(2)
      simp [hS, Finset.sum_range_succ, h0, h1, h2]
      linarith
    | succ n hn' =>
      -- Inductive step: use the original recurrence relation
      rw [show n + 1 + 3 = n + 4 by ring]
      rw [show n + 1 + 2 = n + 3 by ring]
      specialize hn n
      -- From inductive hypothesis, express S(n+2) in terms of S(n+3)
      replace hn' : S (n + 2) = S (n + 3) / 10:= by linarith
      rw [hn'] at hn
      ring_nf at hn
      -- Substitute into the original recurrence and solve
      replace hn : (S (4 + n) + 10 * S (3 + n)) * S (3 + n) * (S (4 + n) - 10 * S (3 + n)) = 0:= by linarith
      have g1:= hSpos (n + 1)
      have g2:= hSpos (n + 2)
      rw [show n + 1 + 2 = 3 + n by ring] at g1
      rw [show n + 2 + 2 = 4 + n by ring] at g2
      simp at hn
      -- Since S(3+n) > 0 and S(4+n) > 0, we must have S(4+n) = 10 * S(3+n)
      rcases hn with hn | hn
      .
        rcases hn with hn | hn
        all_goals
          linarith
      .
        ring_nf
        linarith
  -- From S(n+3) = 10 * S(n+2), derive that a(n+3) = 10 * a(n+2)
  replace hn : ∀ n : ℕ, a (n + 3) = 10 * a (n + 2):= by
    intro n
    have g:= hn n
    specialize hn (n + 1)
    rw [show n + 1 + 3 = n + 4 by ring] at hn
    rw [show n + 1 + 2 = n + 3 by ring] at hn
    -- Use the fact that S(n+4) = S(n+3) + a(n+3) and S(n+3) = S(n+2) + a(n+2)
    rw [hS (n + 3)] at hn
    rw [show n + 3 = n + 2 + 1 by ring] at hn
    rw [Finset.sum_range_succ] at hn
    rw [←hS (n + 2)] at hn
    rw [hS (n + 4)] at hn
    rw [show n + 4 = n + 3 + 1 by ring] at hn
    rw [Finset.sum_range_succ] at hn
    rw [←hS (n + 3)] at hn
    linarith
  -- Prove the explicit formula a(n+2) = 9 * 10^n by induction
  replace hn : ∀ n : ℕ, a (n + 2) = 9 * 10 ^ n:= by
    intro n
    induction n with
    | zero =>
      -- Base case: a(2) = 9 = 9 * 10^0
      simp [h2]
    | succ n hn' =>
      -- Inductive step: a(n+3) = 10 * a(n+2) = 10 * 9 * 10^n = 9 * 10^(n+1)
      rw [show n + 1 + 2 = n + 3 by ring]
      rw [hn n, hn']
      ring_nf
  -- Final step: convert the formula to the required form
  intro n h
  specialize hn (n - 2)
  rw [show n - 2 + 2 = n by omega] at hn
  rw [hn]
