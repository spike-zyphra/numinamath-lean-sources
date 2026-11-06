import Mathlib
/- Let $M$ be a positive integer. Let $[x]$ denote the greatest integer not exceeding $x$ (for example, $[\pi]=3$). Compute the sum $S_M = [\sqrt{1}] + [\sqrt{2}] + \dots + [\sqrt{M^2}]$. Show that $S_M = \frac{M(4M^2-3M+5)}{6}$. -/
theorem algebra_639129 (m : ℕ) (hm : m > 0) : ∑ i in Finset.range (m ^ 2), ⌊√(i + 1)⌋ = m * (4 * m ^ 2 - 3 * m + 5) / 6:= by
  -- It suffices to prove the equation after multiplying both sides by 6
  suffices (∑ i in Finset.range (m ^ 2), ⌊√(i + 1)⌋) * 6 = m * (4 * m ^ 2 - 3 * m + 5) by rw [←this] ; omega
  -- We prove a general statement for any natural number n by induction
  have h1 : ∀ n : ℕ, (∑ i in Finset.range (n ^ 2), ⌊√(i + 1)⌋) * 6 = n * (4 * n ^ 2 - 3 * n + 5):= by
    intro n
    -- Induction on n
    induction n with
    | zero =>
      -- Base case: n = 0, both sides equal 0
      simp
    | succ n ih =>
      -- Inductive step: assume true for n, prove for n+1
      -- Helper lemma: decompose the sum from 0 to (n^2 + k - 1) into two parts
      have h2 : ∀ k : ℕ, ∑ i in Finset.range (n ^ 2), ⌊√(i + 1)⌋ + ∑ i in Finset.range k, ⌊√(n ^ 2 + 1 + i)⌋ = ∑ i in Finset.range (n ^ 2 + k), ⌊√(i + 1)⌋:= by
        intro k
        -- Induction on k to prove the decomposition
        induction k with
        | zero =>
          -- Base case: k = 0
          simp
        | succ k ihk =>
          -- Inductive step for k
          rw [show n ^ 2 + (k + 1) = n ^ 2 + k + 1 by ring]
          rw [Finset.sum_range_succ]
          rw [Finset.sum_range_succ]
          rw [←ihk]
          simp
          rw [show (↑n : ℝ) ^ 2 + 1 + ↑k = ↑n ^ 2 + ↑k + 1 by ring]
          ring
      -- Apply the helper lemma with k = 2n + 1 to get the range for (n+1)^2
      specialize h2 (2 * n + 1)
      rw [show n ^ 2 + (2 * n + 1) = (n + 1) ^ 2 by ring] at h2
      -- Define t as the sum for n^2 terms for clarity
      set t:= ∑ i ∈ Finset.range (n ^ 2), ⌊√(↑i + 1)⌋ with ht
      clear_value t
      rw [←h2]
      simp
      -- Key lemma: compute the sum of floor(sqrt(n^2 + 1 + i)) for i from 0 to 2n
      have h3 : ∑ i ∈ Finset.range (2 * n + 1), ⌊√(↑n ^ 2 + 1 + ↑i)⌋ = 2 * n ^ 2 + n + 1:= by
        -- Split off the last term (i = 2n)
        rw [Finset.sum_range_succ]
        simp
        -- For i = 2n, we have sqrt(n^2 + 1 + 2n) = sqrt((n+1)^2) = n+1
        rw [show ↑n ^ 2 + 1 + 2 * (↑n : ℝ) = (n + 1) ^ 2 by ring]
        rw [show √((n + 1) ^ 2) = n + 1 by field_simp]
        rw [show ⌊(↑n : ℝ) + 1⌋ = n + 1 by field_simp]
        -- For i from 0 to 2n-1, all floor values equal n
        have h4 : ∑ x ∈ Finset.range (2 * n), ⌊√(↑n ^ 2 + 1 + ↑x)⌋ = ∑ _ ∈ Finset.range (2 * n), (↑n : ℤ):= by
          -- Prove that each term in the sum equals n
          have h5 : ∀ x ∈ Finset.range (2 * n), ⌊√(↑n ^ 2 + 1 + ↑x)⌋ = n:= by
            intro x hx
            -- Use the characterization of floor function
            refine Int.floor_eq_iff.mpr ?_
            simp
            constructor
            .
              -- Lower bound: sqrt(n^2 + 1 + x) ≥ n
              have g1 : (↑n : ℝ) ^ 2 + 1 + ↑x ≥ n ^ 2:= by linarith
              replace g1 : √((↑n : ℝ) ^ 2 + 1 + ↑x) ≥ √(n ^ 2):= by exact Real.sqrt_le_sqrt g1
              field_simp at g1
              exact g1
            .
              -- Upper bound: sqrt(n^2 + 1 + x) < n + 1
              rw [show √(↑n ^ 2 + 1 + ↑x) = |√(↑n ^ 2 + 1 + ↑x)| by exact Eq.symm (abs_of_nonneg (by positivity))]
              rw [show (↑n : ℝ) + 1 = |(↑n : ℝ) + 1| by exact Eq.symm (abs_of_nonneg (by positivity))]
              -- This follows from squaring both sides
              suffices √(↑n ^ 2 + 1 + ↑x) ^ 2 < (↑n + 1) ^ 2 by exact sq_lt_sq.mp this
              field_simp
              simp at hx
              rify at hx
              linarith
          exact Finset.sum_congr rfl h5
        simp at h4
        rw [h4]
        ring
      -- Combine everything using the inductive hypothesis and h3
      linarith
  -- Apply the general statement to m
  exact h1 m
