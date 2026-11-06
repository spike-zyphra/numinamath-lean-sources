import Mathlib

/- 14. (YUG) Let $x_{0}=5$ and $x_{n+1}=x_{n}+\frac{1}{x_{n}}(n=0,1,2, \ldots)$. Prove that $45<x_{1000}<45,1$. -/
theorem other_25051 (x : ℕ → ℝ) (h₀ : x 0 = 5) (h₁ : ∀ n, x (n + 1) = x n + 1 / x n) : 45 < x 1000 ∧ x 1000 < 45.1 := by
  -- It suffices to show that x n < √(2*n+25) + 1 / 10 for all n > 0.
  suffices H : ∀ n : ℕ, n > 0 → √(2*n+25) < x n ∧ x n < √(2*n+25) + 1 / 10 by
    -- Take n = 1000 and we get the desired result.
    specialize H 1000
    norm_num at H
    rw [show (2025 : ℝ) = 45 ^ 2 by norm_num] at H
    simp at H
    norm_num at H ⊢
    exact H

  -- Simple lemma that x n > 0 for all n.
  have H₀ (n : ℕ) : x n > 0 := by
    induction n with
    | zero =>
      simp [h₀]
    | succ n ih =>
      simp [h₁]
      positivity

  -- x is strictly increasing.
  have H₁ : StrictMono x := by
    refine strictMono_nat_of_lt_succ fun n ↦ ?_
    simp [h₁ n, H₀ n]

  -- Now we prove the main claim.
  intro n hn
  constructor
  . -- We prove that x n < √(2*n+25) for all n > 0.
    induction n with
    | zero => simp at hn
    | succ n ih =>
      -- We can assume n > 0.
      wlog h : n > 0
      {
        -- The case n = 0 is trivial.
        simp at h
        subst h
        rw [h₁ 0, h₀]
        norm_num
        rw [Real.sqrt_lt' (by norm_num)]
        norm_num
      }
      specialize ih h
      specialize h₁ n
      -- Square both sides at the goal and the inductive hypothesis.
      rw [Real.sqrt_lt' (H₀ _)] at ih ⊢
      specialize H₀ n
      -- (x n + 1 / x n) ^ 2 = x n ^ 2 + 2 + (1 / x n) ^ 2 ≥ x n ^ 2 + 2.
      calc x (n + 1) ^ 2
        _ = (x n + 1 / x n) ^ 2 := by rw [h₁]
        _ = x n ^ 2 + 2 * x n * (1 / x n) + (1 / x n) ^ 2 := by ring
        _ = x n ^ 2 + 2 + (1 / x n) ^ 2 := by simp [ne_of_gt H₀]
        _ > x n ^ 2 + 2 := by linarith only [show (1 / x n) ^ 2 > 0 by positivity]
        _ > 2 * n + 25 + 2 := by linarith only [ih]
        _ = 2 * ↑(n + 1 : ℕ) + 25 := by simp; ring
  . -- We prove that x n < √(2*n+25) + 1 / 10 for all n > 0.
    -- Move a term.
    suffices x n - 1 / 10 < √(2 * ↑n + 25) by linarith
    -- Square both sides.
    apply Real.lt_sqrt_of_sq_lt
    -- It suffices to show that x n ^ 2 ≤ 2 * n + 24 + x n / 5.
    suffices x n ^ 2 ≤ 2 * n + 24 + x n / 5 by linarith
    clear hn
    -- We prove this by induction.
    induction n with
    | zero =>
      -- Base case.
      simp [h₀]
      norm_num
    | succ n ih =>
      -- Inductive step, we suppose the claim holds for n.
      specialize h₁ n
      specialize H₀ n
      -- First, we show that x (n + 1) ^ 2 - x n ^ 2 - (x (n + 1) - x n) / 5 ≤ 2.
      have h : x (n + 1) ^ 2 - x n ^ 2 - (x (n + 1) - x n) / 5 ≤ 2 := by
        calc x (n + 1) ^ 2 - x n ^ 2 - (x (n + 1) - x n) / 5
          -- Some algebraic manipulation.
          _ = (x (n + 1) + x n - 1 / 5) * (x (n + 1) - x n) := by ring
          _ = (2 * x n) * (x (n + 1) - x n) - (x n + 1 / 5 - x (n + 1)) * (x (n + 1) - x n) := by ring
          -- Subtracting a non-positive term.
          _ ≤ (2 * x n) * (x (n + 1) - x n) := by
            rw [sub_le_self_iff, h₁]
            -- Rewrite using the recurrence relation.
            rw [show (x n + 1 / 5 - (x n + 1 / x n)) * (x n + 1 / x n - x n) = (1 / 5 - 1 / x n) * (1 / x n) by ring]
            -- It clearly holds since 1 / x n > 0 and x n ≥ 5.
            refine mul_nonneg ?_ (by positivity)
            simp [-one_div]
            refine one_div_le_one_div_of_le (by simp) ?_
            rw [← h₀]
            exact StrictMono.monotone H₁ (by simp)
          -- Use the recurrence relation to rewrite the term.
          _ = 2 * x n * (1 / x n) := by rw [h₁]; simp
          _ = 2 := by field_simp
      simp
      linarith only [h, ih]
