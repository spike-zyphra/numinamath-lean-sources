import Mathlib
/- If $k$ is an integer, let $\mathrm{c}(k)$ denote the largest cube that is less than or equal to $k$. Find all positive integers $p$ for which the following sequence is bounded:

$$
a_{0}=p \quad \text { and } \quad a_{n+1}=3 a_{n}-2 c\left(a_{n}\right) \quad \text { for } n \geqslant 0
$$

# -/
theorem number_theory_606117 (a : ℕ → ℤ) (c : ℤ → ℤ) (p : ℤ) (hp : p > 0) (hc : ∀ k : ℤ, (∃ q : ℤ, c k = q ^ 3 ∧ q ^ 3 ≤ k ∧ k < (q + 1) ^ 3)) (ha0 : a 0 = p) (ha : ∀ n : ℕ, a (n + 1) = 3 * a n - 2 * c (a n)) : (∃ M : ℤ, (∀ n : ℕ, |a n| ≤ M)) ↔ (∃ k : ℤ, p = k ^ 3):= by
  -- Key lemma: sequence is bounded iff it eventually becomes constant
  have h1 : (∃ M, ∀ (n : ℕ), |a n| ≤ M) ↔ ∃ t : ℕ, ∀ n ≥ t, a (n + 1) = a n:= by
    constructor
    .
      -- Forward direction: if bounded, then eventually constant
      intro h
      rcases h with ⟨M, hM⟩
      by_contra H
      simp at H
      -- Show that sequence is non-decreasing
      replace ha : ∀ n : ℕ, a (n + 1) ≥ a n:= by
        intro n
        replace ha:= ha n
        have g : c (a n) ≤ a n:= by
          replace hc:= hc (a n)
          rcases hc with ⟨q, hq, hq1, -⟩
          linarith
        linarith
      -- Show that sequence grows unboundedly
      have h1 : ∀ m : ℕ, ∃ n : ℕ, a n ≥ m + a 0:= by
        intro m
        induction m with
        | zero =>
          use 0
          simp
        | succ m ih =>
          simp
          rcases ih with ⟨n, hn⟩
          replace H:= H n
          rcases H with ⟨x, hx1, hx2⟩
          have g:= ha x
          replace ha : ∀ k : ℕ, a (n + k) ≥ a n:= by
            intro k
            induction k with
            | zero =>
              simp
            | succ k ih =>
              rw [show n + (k + 1) = n + k + 1 by ring]
              replace ha:= ha (n + k)
              linarith
          replace ha:= ha (x - n)
          rw [show n + (x - n) = x by omega] at ha
          use (x + 1)
          replace g : a (x + 1) > a x:= by omega
          linarith
      replace h1:= h1 (M.natAbs)
      rcases h1 with ⟨n, hn⟩
      simp at hn
      replace hM:= hM n
      have g1 : |a n| ≥ a n:= by exact le_abs_self (a n)
      have g2 : |M| ≥ M:= by exact le_abs_self M
      linarith
    .
      -- Backward direction: if eventually constant, then bounded
      intro h
      rcases h with ⟨t, ht⟩
      -- Show that finite prefix is bounded
      have h1 : ∀ k : ℕ, (∃ M : ℤ, ∀ n : ℕ, n ≤ k → |a n| ≤ M):= by
        intro k
        induction k with
        | zero =>
          simp
          use |a 0|
        | succ k ih =>
          rcases ih with ⟨M, hM⟩
          use max M |a (k + 1)|
          intro n hn
          by_cases hn1 : n = k + 1
          .
            subst n
            exact Int.le_max_right M |a (k + 1)|
          .
            replace hM:= hM n (by omega)
            suffices M ≤ max M |a (k + 1)| by linarith
            exact Int.le_max_left M |a (k + 1)|
      replace h1:= h1 t
      simp at h1
      rcases h1 with ⟨M, hM⟩
      use M
      intro n
      by_cases hn : n ≤ t
      .
        exact hM n hn
      .
        simp at hn
        -- Show that sequence is constant after t
        have h1 : ∀ m : ℕ, a (t + m) = a t:= by
          intro m
          induction m with
          | zero =>
            simp
          | succ m ih =>
            rw [show t + (m + 1) = t + m + 1 by omega]
            replace ht:= ht (t + m) (by omega)
            linarith
        replace h1:= h1 (n - t)
        rw [show t + (n - t) = n by omega] at h1
        replace hM:= hM t (by omega)
        rw [h1]
        exact hM
  -- Lemma: c(k) = k if and only if k is a perfect cube
  have h2 : ∀ k : ℤ, (c k = k ↔ ∃ s : ℤ, k = s ^ 3):= by
    intro k
    constructor
    .
      -- If c(k) = k, then k is a perfect cube
      intro h
      replace hc:= hc k
      rcases hc with ⟨q, hq, -, -⟩
      use q
      linarith
    .
      -- If k is a perfect cube, then c(k) = k
      intro h
      rcases h with ⟨s, hs⟩
      replace hc:= hc k
      rcases hc with ⟨q, hq, hq1, hq2⟩
      replace hq1 : (s - q) * (s ^ 2 + q ^ 2 + (s + q) ^ 2) ≥ 0:= by linarith
      replace hq2 : (q + 1 - s) * (s ^ 2 + (q + 1) ^ 2 + (s + q + 1) ^ 2) > 0:= by linarith
      by_cases h1 : s = 0 ∧ q = 0
      .
        rcases h1 with ⟨rfl, rfl⟩
        subst k
        exact hq
      .
        have h2 : s ^ 2 + q ^ 2 + (s + q) ^ 2 > 0:= by
          by_contra H
          have H1 : s ^ 2 = 0:= by linarith [sq_nonneg s, sq_nonneg q, sq_nonneg (s + q)]
          have H2 : q ^ 2 = 0:= by linarith [sq_nonneg s, sq_nonneg q, sq_nonneg (s + q)]
          simp at H1 H2
          subst s q
          simp at h1
        have h3 : s ^ 2 + (q + 1) ^ 2 + (s + q + 1) ^ 2 > 0:= by
          have h3 : s ^ 2 + (q + 1) ^ 2 + (s + q + 1) ^ 2 ≥ 0:= by positivity
          by_contra H
          replace H : s ^ 2 + (q + 1) ^ 2 + (s + q + 1) ^ 2 = 0:= by linarith
          rw [H] at hq2
          simp at hq2
        replace hq1 : s - q ≥ 0:= by exact (Int.mul_nonneg_iff_of_pos_right h2).mp hq1
        replace hq2 : q + 1 - s > 0:= by exact (pos_iff_pos_of_mul_pos hq2).mpr h3
        replace hq1 : s = q:= by omega
        subst s
        linarith
  -- Lemma: c(k) ≤ k for all k
  have h3 : ∀ k : ℤ, c k ≤ k:= by
    intro k
    replace hc:= hc k
    rcases hc with ⟨q, hq, hq1, -⟩
    linarith
  -- Lemma: all terms of the sequence are positive
  have h4 : ∀ n : ℕ, a n > 0:= by
    intro n
    induction n with
    | zero =>
      linarith
    | succ n ih =>
      replace ha:= ha n
      replace h3:= h3 (a n)
      linarith
  -- Strengthen hc to ensure q ≥ 0
  replace hc : ∀ n : ℕ, (∃ q : ℤ, q ≥ 0 ∧ c (a n) = q ^ 3 ∧ q ^ 3 ≤ a n ∧ a n < (q + 1) ^ 3):= by
    intro n
    replace hc:= hc (a n)
    rcases hc with ⟨q, hq, hq1, hq2⟩
    replace h4:= h4 n
    use q
    refine ⟨?_, hq, hq1, hq2⟩
    by_contra H
    replace H : -q - 1 ≥ 0:= by omega
    replace H : (-q - 1) ^ 3 ≥ 0:= by positivity
    linarith
  constructor
  .
    -- Forward direction: if bounded, then p is a perfect cube
    intro h
    replace h:= h1.1 h
    by_contra H
    -- Show that sequence is strictly increasing
    have h5 : ∀ n : ℕ, a (n + 1) > a n:= by
      intro n
      induction n with
      | zero =>
        simp
        replace ha:= ha 0
        simp at ha
        by_contra H1
        replace h3:= h3 (a 0)
        simp at H1
        replace H1 : c (a 0) = a 0:= by linarith
        replace h2:= (h2 (a 0)).1 H1
        rw [ha0] at h2
        trivial
      | succ n ih =>
        by_contra H1
        have g:= ha n
        replace ha:= ha (n + 1)
        replace h3:= h3 (a (n + 1))
        replace h3 : c (a (n + 1)) = a (n + 1):= by linarith
        replace h2:= (h2 (a (n + 1))).1 h3
        replace hc:= hc n
        rcases hc with ⟨q, hq, hq1, -, hq3⟩
        rcases h2 with ⟨s, hs⟩
        have g1 : s > q:= by
          replace ih : (s - q) * (s ^ 2 + q ^ 2 + (s + q) ^ 2) > 0:= by linarith
          have g2 : s ^ 2 + q ^ 2 + (s + q) ^ 2 ≥ 0:= by positivity
          replace ih : s - q > 0:= by exact pos_of_mul_pos_left ih g2
          linarith
        replace g2 : s < q + 3:= by
          replace g : (q + 3 - s) * ((q + 3) ^ 2 + s ^ 2 + (q + 3 + s) ^ 2) > 0:= by linarith
          have g2 : (q + 3) ^ 2 + s ^ 2 + (q + 3 + s) ^ 2 ≥ 0:= by positivity
          replace g : q + 3 - s > 0:= by exact pos_of_mul_pos_left g g2
          linarith
        replace g2 : s = q + 1 ∨ s = q + 2:= by omega
        replace g : 3 ∣ a (n + 1) + 2 * c (a n):= by
          use a n
          linarith
        rcases g2 with rfl | rfl
        all_goals
          rw [hs, hq1] at g
          ring_nf at g
          omega
    rcases h with ⟨t, ht⟩
    replace ht:= ht t (by omega)
    replace h5:= h5 t
    linarith
  .
    -- Backward direction: if p is a perfect cube, then bounded
    intro h
    apply h1.2
    use 0
    simp
    rw [←ha0] at h
    intro n
    induction n with
    | zero =>
      simp
      rw [ha 0]
      replace h2:= (h2 (a 0)).2 h
      linarith
    | succ n ih =>
      rw [ha (n + 1)]
      suffices c (a (n + 1)) = a (n + 1) by linarith
      rw [ih]
      rw [ha n] at ih
      linarith
