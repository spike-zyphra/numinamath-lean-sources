import Mathlib
/- 5. For what positive integer $k$ does $\frac{20^{k}+18^{k}}{k!}$ achieve its maximum value?
(Hong Kong, China) -/
theorem algebra_184870 (f : ℕ → ℝ) (hf : ∀ k, f k = (20 ^ k + 18 ^ k) / Nat.factorial k) :
{k : ℕ | IsMaxOn f (Set.univ : Set ℕ) k} = {19}:= by
  -- We prove equality of sets by showing each is a subset of the other
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
    -- We need to show f(k+1) > f(k), which we'll prove by cross-multiplication
    suffices ((20 : ℝ) ^ k + 18 ^ k) / ↑k.factorial * (k + 1).factorial < (20 ^ (k + 1) + 18 ^ (k + 1)) by exact (lt_div_iff₀ g2).mpr this
    -- Use the recurrence relation for factorial: (k+1)! = (k+1)·k!
    rw [show (k + 1).factorial = (k + 1) * k.factorial by exact Nat.factorial_succ k]
    field_simp
    -- Simplify the expression
    rw [show ((20 : ℝ) ^ k + 18 ^ k) * ((↑k + 1) * ↑k.factorial) / ↑k.factorial  = ((20 : ℝ) ^ k + 18 ^ k) * (↑k + 1) by field_simp ; linarith]
    ring_nf
    -- After algebraic manipulation, we need to show this inequality
    suffices (20 : ℝ) ^ k * (19 - k) + 18 ^ k * (17 - k) > 0 by linarith
    -- Handle the case k = 18 separately
    by_cases hk : k = 18
    .
      -- When k = 18, we use the fact that 20 > 18
      have g3 : (20 : ℝ) > 18:= by norm_num
      replace g3 : (20 : ℝ) ^ k > 18 ^ k:= by refine pow_lt_pow_left g3 (by linarith) (by linarith)
      set A:= (20 : ℝ) ^ k
      set B:= (18 : ℝ) ^ k
      clear_value A B
      subst k
      simp
      linarith
    .
      -- When k ≤ 17, both terms in our sum are non-negative, with at least one positive
      replace h : k ≤ 17:= by omega
      rify at h
      replace h : 17 - (↑k : ℝ) ≥ 0:= by linarith
      have h1 : 19 - (↑k : ℝ) > 0:= by linarith
      replace h1 : (20 : ℝ) ^ k * (19 - k) > 0:= by positivity
      replace h : (18 : ℝ) ^ k * (17 - k) ≥ 0:= by positivity
      linarith

  -- Next, we prove that f is strictly decreasing for k ≥ 19
  have h2 : ∀ k : ℕ, k ≥ 19 → f (k + 1) < f k:= by
    intro k hk
    -- Establish that factorials are positive
    have g1 : k.factorial > 0:= by exact Nat.factorial_pos k
    have g2 : (k + 1).factorial > 0:= by exact Nat.factorial_pos (k + 1)
    rify at g1 g2
    simp [hf]
    -- We need to show f(k+1) < f(k), which we'll prove by cross-multiplication
    suffices ((20 : ℝ) ^ k + 18 ^ k) / ↑k.factorial * (k + 1).factorial > (20 ^ (k + 1) + 18 ^ (k + 1)) by exact (div_lt_iff₀ g2).mpr this
    -- Use the recurrence relation for factorial: (k+1)! = (k+1)·k!
    rw [show (k + 1).factorial = (k + 1) * k.factorial by exact Nat.factorial_succ k]
    field_simp
    -- Simplify the expression
    rw [show ((20 : ℝ) ^ k + 18 ^ k) * ((↑k + 1) * ↑k.factorial) / ↑k.factorial  = ((20 : ℝ) ^ k + 18 ^ k) * (↑k + 1) by field_simp ; linarith]
    ring_nf
    -- After algebraic manipulation, we need to show this inequality
    suffices (20 : ℝ) ^ k * (k - 19) + 18 ^ k * (k - 17) > 0 by linarith
    -- For k ≥ 19, both terms in our sum are non-negative, with at least one positive
    rify at hk
    replace hk : (↑k : ℝ) - 19 ≥ 0:= by linarith
    have hk1 : (↑k : ℝ) - 17 > 0:= by linarith
    replace hk : (20 : ℝ) ^ k * (k - 19) ≥ 0:= by positivity
    replace hk1 : (18 : ℝ) ^ k * (k - 17) > 0:= by positivity
    linarith

  -- From the above, we can conclude that f(k) < f(19) for all k ≠ 19
  replace h1 : ∀ k : ℕ, k ≠ 19 → f k < f 19:= by
    intro k hk
    -- Split into cases: k < 19 or k > 19
    replace hk : k < 19 ∨ k > 19:= by omega
    rcases hk with hk | hk
    .
      -- For k < 19, we use induction to show f(k) < f(19)
      have h2 : ∀ m : ℕ, f (18 - m) < f 19:= by
        intro m
        induction m with
        | zero =>
          simp
          specialize h1 18
          simp at h1
          exact h1
        | succ m ih =>
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
      specialize h2 (18 - k)
      rw [show 18 - (18 - k) = k by omega] at h2
      exact h2
    .
      -- For k > 19, we use induction to show f(k) < f(19)
      have h2 : ∀ m : ℕ, f (20 + m) < f 19:= by
        intro m
        induction m with
        | zero =>
          specialize h2 19 (by omega)
          simp at h2
          simp
          exact h2
        | succ m ih =>
          rw [show 20 + (m + 1) = 20 + m + 1 by omega]
          specialize h2 (20 + m) (by omega)
          linarith
      specialize h2 (k - 20)
      rw [show 20 + (k - 20) = k by omega] at h2
      exact h2

  -- Now we prove the two directions of set equality
  constructor
  .
    -- First direction: if k is a maximum point, then k = 19
    intro h
    simp at h
    simp
    by_contra H
    specialize h1 k H
    replace h : f 19 ≤ f k:= by exact h trivial
    linarith
  .
    -- Second direction: if k = 19, then k is a maximum point
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
