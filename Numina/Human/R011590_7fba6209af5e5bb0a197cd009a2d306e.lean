import Mathlib
/- B1. Find all integer solutions of the equation $m^{4}+2 n^{2}=9 m n$. -/
theorem number_theory_136633 : {(m, n) : ℤ × ℤ | m ^ 4 + 2 * n ^ 2 = 9 * m * n} = {(0, 0), (2, 1), (-2, -1), (2, 8), (-2, -8), (3, 9), (-3, -9)}:= by
  -- Use extensionality to prove equality of sets by showing that an arbitrary pair (m,n) is in the first set if and only if it's in the second set
  ext ⟨m, n⟩
  constructor
  -- Forward direction: if (m,n) satisfies the equation, then it's one of the listed pairs
  .
    intro h
    simp at h
    -- Rearrange the equation to a form that's easier to analyze
    replace h : (4 * n - 9 * m) ^ 2 = (81 - 8 * m ^ 2) * m ^ 2:= by linarith
    -- This helper lemma handles the case where m ≥ 0
    have h1 : ∀ m n : ℤ, m ≥ 0 → (4 * n - 9 * m) ^ 2 = (81 - 8 * m ^ 2) * m ^ 2 → ((m, n) = (0, 0) ∨ (m, n) = (2, 1) ∨ (m, n) = (2, 8) ∨ (m, n) = (3, 9)):= by
      intro m n hm h
      -- The right side of the equation must be non-negative since it equals a square
      have g1 : (81 - 8 * m ^ 2) * m ^ 2 ≥ 0:= by
        rw [←h]
        positivity
      -- Case analysis: either m = 0 or m > 0
      by_cases h2 : m = 0
      -- Case: m = 0
      .
        subst m
        simp at h
        subst n
        simp
      -- Case: m > 0
      .
        replace hm : m > 0:= by omega
        replace h2 : m ^ 2 > 0:= by positivity
        -- Since m^2 > 0 and (81 - 8m^2)m^2 ≥ 0, we must have 81 - 8m^2 ≥ 0
        replace g1 : 81 - 8 * m ^ 2 ≥ 0:= by exact (Int.mul_nonneg_iff_of_pos_right h2).mp g1
        -- This inequality implies m ≤ 3
        replace g1 : m ≤ 3:= by
          by_contra H
          simp at H
          replace H : m ≥ 4:= by linarith
          replace H : m ^ 2 ≥ 4 ^ 2:= by nlinarith only [H]
          linarith
        -- So m must be 1, 2, or 3
        replace g1 : m = 1 ∨ m = 2 ∨ m = 3:= by omega
        rcases g1 with g1 | g1 | g1
        -- Subcase: m = 1
        .
          subst m
          simp at h
          rw [show (4 * n - 9) ^ 2 = |4 * n - 9| ^ 2 by exact Eq.symm (sq_abs (4 * n - 9))] at h
          set a:= |4 * n - 9| with ha
          clear_value a
          replace ha : a ≥ 0:= by rw [ha] ; positivity
          -- Derive a contradiction by showing a must be both > 8 and < 9
          have ha1 : a > 8:= by
            by_contra H
            simp at H
            replace H : a ^ 2 ≤ 64:= by nlinarith only [H, ha]
            linarith
          have ha2 : a < 9:= by
            by_contra H
            simp at H
            replace H : a ^ 2 ≥ 81:= by nlinarith only [H, ha]
            linarith
          linarith
        -- Subcase: m = 2
        .
          subst m
          simp at h
          -- The equation simplifies to (n-1)(n-8) = 0, so n = 1 or n = 8
          replace h : (n - 1) * (n - 8) = 0:= by linarith
          simp at h
          rcases h with h | h
          .
            replace h : n = 1:= by omega
            subst n
            simp
          .
            replace h : n = 8:= by omega
            subst n
            simp
        -- Subcase: m = 3
        .
          subst m
          simp at h
          -- The equation simplifies to (2n-9)(n-9) = 0
          replace h : (2 * n - 9) * (n - 9) = 0:= by linarith
          simp at h
          rcases h with h | h
          .
            replace h : 2 * n = 9:= by omega
            -- But 2 doesn't divide 9, so this is impossible
            replace h : (2 : ℤ) ∣ 9:= by rw [←h] ; simp
            omega
          .
            replace h : n = 9:= by omega
            subst n
            simp
    -- Now handle both cases: m ≥ 0 and m < 0
    by_cases h2 : m ≥ 0
    -- Case: m ≥ 0, use the helper lemma directly
    .
      specialize h1 m n h2 h
      rcases h1 with h1 | h1 | h1 | h1
      all_goals
        simp at h1
        rcases h1 with ⟨gm, gn⟩
        subst m n
        simp
    -- Case: m < 0, use the helper lemma with -m and -n
    .
      set M:= -m with hM
      set N:= -n with hN
      clear_value M N
      replace hM : m = -M:= by omega
      replace hN : n = -N:= by omega
      subst m n
      simp at h2 h
      -- Apply the helper lemma to M and N, which gives us the negative solutions
      specialize h1 M N (by linarith) (by linarith)
      rcases h1 with h1 | h1 | h1 | h1
      all_goals
        simp at h1
        rcases h1 with ⟨gm, gn⟩
        subst M N
        simp
  -- Backward direction: verify that each of the listed pairs satisfies the equation
  .
    intro h
    simp at h
    rcases h with h | h | h | h | h | h | h
    all_goals
      rcases h with ⟨gm, gn⟩
      subst m n
      simp
