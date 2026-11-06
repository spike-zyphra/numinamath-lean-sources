import Mathlib
/- 3. Given the function $f(n)=\frac{20^{n}+3^{n}}{n!}, n \in \mathbf{N}$. Then, the value of $n$ that maximizes $f(n)$ is, $n=$-/
theorem algebra_318040 (f : ℕ → ℝ) (hf : ∀ k, f k = (20 ^ k + 3 ^ k) / Nat.factorial k) :
{k : ℕ | IsMaxOn f (Set.univ : Set ℕ) k} = {19}:= by
  ext k
  -- First, we prove that f is strictly increasing for k ≤ 18
  have h1 : ∀ k : ℕ, k ≤ 18 → f (k + 1) > f k:= by
    intro k
    -- Establish that factorials are positive
    have g1 : k.factorial > 0:= by exact Nat.factorial_pos k
    have g2 : (k + 1).factorial > 0:= by exact Nat.factorial_pos (k + 1)
    rify at g1 g2
    intro h
    simp [hf]
    -- Show that f(k+1) > f(k) by comparing the expressions
    suffices ((20 : ℝ) ^ k + 3 ^ k) / ↑k.factorial * (k + 1).factorial < (20 ^ (k + 1) + 3 ^ (k + 1)) by exact (lt_div_iff₀ g2).mpr this
    -- Use the factorial recurrence relation
    rw [show (k + 1).factorial = (k + 1) * k.factorial by exact Nat.factorial_succ k]
    field_simp
    -- Simplify the algebraic expression
    rw [show ((20 : ℝ) ^ k + 3 ^ k) * ((↑k + 1) * ↑k.factorial) / ↑k.factorial  = ((20 : ℝ) ^ k + 3 ^ k) * (↑k + 1) by field_simp ; linarith]
    ring_nf
    -- The inequality reduces to showing 20^k * (19 - k) + 3^k * (2 - k) > 0
    suffices (20 : ℝ) ^ k * (19 - k) + 3 ^ k * (2 - k) > 0 by linarith
    -- Case analysis: k ≤ 2 or k > 2
    by_cases hk : k ≤ 2
    .
      -- For k ≤ 2, both terms are non-negative with at least one positive
      have g3 : 19 > k := by omega
      rify at g3 hk
      replace g3 : 19 - (↑k : ℝ) > 0:= by linarith
      have g4 : 2 - (↑k : ℝ) ≥ 0:= by linarith
      positivity
    .
      -- For k > 2, we show that 20^k * (19 - k) dominates 3^k * (k - 2)
      simp at hk
      have g1 : 19 - (↑k : ℝ) ≥ 1:= by
        rify at h
        linarith
      -- Lower bound for the first term
      replace g1 : (20 : ℝ) ^ k * (19 - k) ≥ 20 ^ k:= by
        have g2 : (20 : ℝ) ^ k ≥ 0:= by positivity
        exact le_mul_of_one_le_right g2 g1
      -- Upper bound for the second term
      have g2 : (↑k : ℝ) - 2 ≤ 16:= by
        rify at h
        linarith
      replace g2 : 3 ^ k * ((↑k : ℝ) - 2) ≤ 3 ^ k * 16:= by
        have g3 : (3 : ℝ) ^ k ≥ 0:= by positivity
        exact mul_le_mul_of_nonneg_left g2 g3
      -- Show that 20^k > 3^k * 16, which implies the desired inequality
      suffices (20 : ℝ) ^ k > 3 ^ k * 16 by linarith
      -- Substitute k = k1 + 3 to simplify the proof
      set k1:= k - 3 with hk1
      clear_value k1
      replace hk1 : k = k1 + 3:= by omega
      subst k
      ring_nf
      -- Use the fact that 20 > 3
      have g3 : (20 : ℝ) > 3:= by norm_num
      by_cases hk1 : k1 = 0
      .
        -- Base case: k1 = 0 (i.e., k = 3)
        subst k1
        norm_num
      .
        -- Inductive case: use the fact that (20/3)^k1 grows exponentially
        replace g3 : (20 : ℝ) ^ k1 > 3 ^ k1:= by refine pow_lt_pow_left g3 (by linarith) hk1
        have g4 : (3 : ℝ) ^ k1 > 0:= by positivity
        linarith
  -- Second, we prove that f is strictly decreasing for k ≥ 19
  have h2 : ∀ k : ℕ, k ≥ 19 → f (k + 1) < f k:= by
    intro k hk
    -- Establish that factorials are positive
    have g1 : k.factorial > 0:= by exact Nat.factorial_pos k
    have g2 : (k + 1).factorial > 0:= by exact Nat.factorial_pos (k + 1)
    rify at g1 g2
    simp [hf]
    -- Show that f(k+1) < f(k) by comparing the expressions
    suffices ((20 : ℝ) ^ k + 3 ^ k) / ↑k.factorial * (k + 1).factorial > (20 ^ (k + 1) + 3 ^ (k + 1)) by exact (div_lt_iff₀ g2).mpr this
    -- Use the factorial recurrence relation
    rw [show (k + 1).factorial = (k + 1) * k.factorial by exact Nat.factorial_succ k]
    field_simp
    -- Simplify the algebraic expression
    rw [show ((20 : ℝ) ^ k + 3 ^ k) * ((↑k + 1) * ↑k.factorial) / ↑k.factorial  = ((20 : ℝ) ^ k + 3 ^ k) * (↑k + 1) by field_simp ; linarith]
    ring_nf
    -- The inequality reduces to showing 20^k * (k - 19) + 3^k * (k - 2) > 0
    suffices (20 : ℝ) ^ k * (k - 19) + 3 ^ k * (k - 2) > 0 by linarith
    -- For k ≥ 19, both terms are positive
    rify at hk
    replace hk : (↑k : ℝ) - 19 ≥ 0:= by linarith
    have hk1 : (↑k : ℝ) - 2 > 0:= by linarith
    replace hk : (20 : ℝ) ^ k * (k - 19) ≥ 0:= by positivity
    replace hk1 : (3 : ℝ) ^ k * (k - 2) > 0:= by positivity
    linarith
  -- Combine the results to show that f(k) < f(19) for all k ≠ 19
  replace h1 : ∀ k : ℕ, k ≠ 19 → f k < f 19:= by
    intro k hk
    -- Case analysis: k < 19 or k > 19
    replace hk : k < 19 ∨ k > 19:= by omega
    rcases hk with hk | hk
    .
      -- For k < 19, use the increasing property to show f(k) < f(19)
      have h2 : ∀ m : ℕ, f (18 - m) < f 19:= by
        intro m
        induction m with
        | zero =>
          -- Base case: f(18) < f(19)
          simp
          specialize h1 18
          simp at h1
          exact h1
        | succ m ih =>
          -- Inductive step: if f(18 - m) < f(19), then f(18 - (m+1)) < f(19)
          by_cases hm : m < 18
          .
            rw [show 18 - m = 18 - (m + 1) + 1 by omega] at ih
            specialize h1 (18 - (m + 1))
            replace h1:= h1 (by omega)
            linarith
          .
            simp at hm
            rw [show 18 - m = 0 by omega] at ih
            rw [show 18 - (m + 1) = 0 by omega]
            exact ih
      -- Apply the result to k
      specialize h2 (18 - k)
      rw [show 18 - (18 - k) = k by omega] at h2
      exact h2
    .
      -- For k > 19, use the decreasing property to show f(k) < f(19)
      have h2 : ∀ m : ℕ, f (20 + m) < f 19:= by
        intro m
        induction m with
        | zero =>
          -- Base case: f(20) < f(19)
          specialize h2 19 (by omega)
          simp at h2
          simp
          exact h2
        | succ m ih =>
          -- Inductive step: if f(20 + m) < f(19), then f(20 + (m+1)) < f(19)
          rw [show 20 + (m + 1) = 20 + m + 1 by omega]
          specialize h2 (20 + m) (by omega)
          linarith
      -- Apply the result to k
      specialize h2 (k - 20)
      rw [show 20 + (k - 20) = k by omega] at h2
      exact h2

  -- Finally, prove the set equality by showing both directions
  constructor
  .
    -- If k is a maximizer, then k = 19
    intro h
    simp at h
    simp
    by_contra H
    specialize h1 k H
    replace h : f 19 ≤ f k:= by exact h trivial
    linarith
  .
    -- If k = 19, then k is a maximizer
    intro h
    simp at h
    subst k
    simp
    intro x hx
    simp
    clear hx
    by_cases hx : x = 19
    .
      subst x
      simp
    .
      linarith only [h1 x hx]
