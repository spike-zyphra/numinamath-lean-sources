import Mathlib
/- Let $M$ be an integer greater than 1. Let $N = M^2$. Let $S = \sum_{k=1}^{N_0} \lfloor \sqrt{k} \rfloor$. Show that $\lfloor \sqrt{S} \rfloor = \left\lfloor \sqrt{\frac{M(M-1)(4M+1)}{6} + M} \right\rfloor$. Verify this formula for $M=5$, for which the value of $\lfloor \sqrt{S} \rfloor$ is 8. -/
theorem number_theory_638842 (m : ℕ) (hm : m > 1) : ⌊√(∑ i in Finset.range (m ^ 2), ⌊√(i + 1)⌋)⌋ = ⌊√(m * (m - 1) * (4 * m + 1) / 6 + m)⌋:= by
  -- Key lemma: The sum multiplied by 6 equals m * (4m^2 - 3m + 5)
  have h1 : (∑ i in Finset.range (m ^ 2), ⌊√(i + 1)⌋) * 6 = m * (4 * m ^ 2 - 3 * m + 5):= by
    -- Prove the formula for all natural numbers n
    have h1 : ∀ n : ℕ, (∑ i in Finset.range (n ^ 2), ⌊√(i + 1)⌋) * 6 = n * (4 * n ^ 2 - 3 * n + 5):= by
      intro n
      -- Use mathematical induction on n
      induction n with
      | zero =>
        -- Base case: n = 0
        simp
      | succ n ih =>
        -- Inductive step: prove for n+1 using the inductive hypothesis
        -- Lemma: splitting the sum into two parts
        have h2 : ∀ k : ℕ, ∑ i in Finset.range (n ^ 2), ⌊√(i + 1)⌋ + ∑ i in Finset.range k, ⌊√(n ^ 2 + 1 + i)⌋ = ∑ i in Finset.range (n ^ 2 + k), ⌊√(i + 1)⌋:= by
          intro k
          -- Use induction on k to prove the splitting lemma
          induction k with
          | zero =>
            -- Base case: k = 0
            simp
          | succ k ihk =>
            -- Inductive step for k+1
            rw [show n ^ 2 + (k + 1) = n ^ 2 + k + 1 by ring]
            rw [Finset.sum_range_succ]
            rw [Finset.sum_range_succ]
            rw [←ihk]
            simp
            rw [show (↑n : ℝ) ^ 2 + 1 + ↑k = ↑n ^ 2 + ↑k + 1 by ring]
            ring
        -- Apply the splitting lemma with k = 2n + 1
        specialize h2 (2 * n + 1)
        rw [show n ^ 2 + (2 * n + 1) = (n + 1) ^ 2 by ring] at h2
        -- Define t as the sum for the first n^2 terms
        set t:= ∑ i ∈ Finset.range (n ^ 2), ⌊√(↑i + 1)⌋ with ht
        clear_value t
        rw [←h2]
        simp
        -- Key calculation: sum of floor square roots for the range [n^2+1, (n+1)^2]
        have h3 : ∑ i ∈ Finset.range (2 * n + 1), ⌊√(↑n ^ 2 + 1 + ↑i)⌋ = 2 * n ^ 2 + n + 1:= by
          rw [Finset.sum_range_succ]
          simp
          rw [show ↑n ^ 2 + 1 + 2 * (↑n : ℝ) = (n + 1) ^ 2 by ring]
          rw [show √((n + 1) ^ 2) = n + 1 by field_simp]
          rw [show ⌊(↑n : ℝ) + 1⌋ = n + 1 by field_simp]
          -- Calculate the sum for the first 2n terms (all equal to n)
          have h4 : ∑ x ∈ Finset.range (2 * n), ⌊√(↑n ^ 2 + 1 + ↑x)⌋ = ∑ _ ∈ Finset.range (2 * n), (↑n : ℤ):= by
            -- Prove that each term in the range equals n
            have h5 : ∀ x ∈ Finset.range (2 * n), ⌊√(↑n ^ 2 + 1 + ↑x)⌋ = n:= by
              intro x hx
              refine Int.floor_eq_iff.mpr ?_
              simp
              constructor
              .
                -- Prove the lower bound: √(n^2 + 1 + x) ≥ n
                have g1 : (↑n : ℝ) ^ 2 + 1 + ↑x ≥ n ^ 2:= by linarith
                replace g1 : √((↑n : ℝ) ^ 2 + 1 + ↑x) ≥ √(n ^ 2):= by exact Real.sqrt_le_sqrt g1
                field_simp at g1
                exact g1
              .
                -- Prove the upper bound: √(n^2 + 1 + x) < n + 1
                rw [show √(↑n ^ 2 + 1 + ↑x) = |√(↑n ^ 2 + 1 + ↑x)| by exact Eq.symm (abs_of_nonneg (by positivity))]
                rw [show (↑n : ℝ) + 1 = |(↑n : ℝ) + 1| by exact Eq.symm (abs_of_nonneg (by positivity))]
                suffices √(↑n ^ 2 + 1 + ↑x) ^ 2 < (↑n + 1) ^ 2 by exact sq_lt_sq.mp this
                field_simp
                simp at hx
                rify at hx
                linarith
            exact Finset.sum_congr rfl h5
          simp at h4
          rw [h4]
          ring
        linarith
    -- Apply the general formula to our specific m
    exact h1 m
  -- Convert the result to real numbers and complete the proof
  suffices ∑ i ∈ Finset.range (m ^ 2), (↑⌊√(↑i + 1)⌋ : ℝ) = ↑m * (↑m - 1) * (4 * ↑m + 1) / 6 + ↑m by rw [this]
  rify at h1
  linarith
