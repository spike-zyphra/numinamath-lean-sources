import Mathlib
/- Let $a_{1}=1$, and let $a_{n}=\left\lfloor n^{3} / a_{n-1}\right\rfloor$ for $n>1$. Determine the value of $a_{999}$. -/
theorem number_theory_611089 (a : ℕ → ℤ) (h1 : a 1 = 1) (hn : ∀ n : ℕ, n > 1 → a n = ⌊(n ^ 3) / (↑(a (n - 1)) : ℝ)⌋) : a 999 = 999:= by
  -- We prove that for all n, a(2n+1) = 2n+1
  have h2 : ∀ n : ℕ, a (2 * n + 1) = 2 * n + 1:= by
    intro n
    induction n with
    | zero =>
      -- Base case: n = 0, so a(2*0+1) = a(1) = 1
      simp [h1]
    | succ n ih =>
      -- Inductive case: assume a(2n+1) = 2n+1, prove a(2(n+1)+1) = 2(n+1)+1
      by_cases h : n = 0
      .
        -- Special case: n = 0, so we need to prove a(3) = 3
        subst n
        simp
        rw [hn 3 (by omega), hn 2 (by omega), h1]
        simp
        norm_num
      .
        -- General case: n > 0
        -- First we compute a(2n+2)
        have h2:= hn (2 * n + 2) (by omega)
        rw [show 2 * n + 2 - 1 = 2 * n + 1 by omega] at h2
        rw [ih] at h2
        simp at h2
        -- Establish some inequalities we'll need
        have g1 : 2 * n + 1 > 0:= by omega
        have g2 : n ^ 2 ≥ 0:= by omega
        have g3 : n ^ 3 ≥ 0:= by omega
        have g4 : (2 * n + 1) ^ 2 + 3 * (2 * n + 1) + 3 > 0:= by positivity
        replace h : n > 0:= by omega
        rify at g1 g2 g3 g4 h
        -- Prove that a(2n+2) = (2n+1)² + 3(2n+1) + 3
        have h3 : a (2 * n + 2) = (2 * n + 1) ^ 2 + 3 * (2 * n + 1) + 3:= by
          rw [h2]
          refine Int.floor_eq_iff.mpr ?_
          constructor
          .
            -- Prove the lower bound for the floor function
            field_simp
            suffices ((2 * ↑n + 1) ^ 2 + 3 * (2 * ↑n + 1) + 3) * (2 * ↑n + 1) ≤ (2 * (↑n : ℝ) + 2) ^ 3 by exact (le_div_iff₀ g1).mpr this
            ring_nf
            linarith
          .
            -- Prove the upper bound for the floor function
            simp
            suffices (2 * (↑n : ℝ) + 2) ^ 3 < ((2 * ↑n + 1) ^ 2 + 3 * (2 * ↑n + 1) + 3 + 1) * (2 * ↑n + 1) by exact (div_lt_iff₀ g1).mpr this
            ring_nf
            linarith
        -- Now compute a(2n+3) using a(2n+2)
        rw [show 2 * (n + 1) + 1 = 2 * n + 3 by omega]
        rw [hn (2 * n + 3) (by omega)]
        rw [show 2 * n + 3 - 1 = 2 * n + 2 by omega]
        rw [h3]
        simp
        refine Int.floor_eq_iff.mpr ?_
        constructor
        .
          -- Prove the lower bound for the floor function
          simp
          suffices (2 * (↑n + 1) + 1) * ((2 * ↑n + 1) ^ 2 + 3 * (2 * ↑n + 1) + 3) ≤ (2 * (↑n : ℝ) + 3) ^ 3 by exact (le_div_iff₀ g4).mpr this
          ring_nf
          linarith
        .
          -- Prove the upper bound for the floor function
          simp
          suffices (2 * (↑n : ℝ) + 3) ^ 3 < (2 * (↑n + 1) + 1 + 1) * ((2 * ↑n + 1) ^ 2 + 3 * (2 * ↑n + 1) + 3) by exact (div_lt_iff₀ g4).mpr this
          ring_nf
          linarith
  -- Apply the result to n = 499, which gives a(2*499+1) = a(999) = 2*499+1 = 999
  specialize h2 499
  simp at h2
  exact h2
