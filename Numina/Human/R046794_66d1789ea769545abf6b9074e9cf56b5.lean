import Mathlib
/- 8. Given an even function $f: \mathbf{Z} \rightarrow \mathbf{Z}$ that satisfies $f(1)=1, f(2008) \neq 1$, and for any integers $a, b$, $f(a+b) \leqslant \max \{f(a), f(b)\}$, then the possible value of $f(2009)$ is -/
theorem number_theory_180117 (f : ℤ → ℤ) (h₀ : ∀ x, f (-x) = f x) (h₁ : f 1 = 1)
    (h₂ : f 2008 ≠ 1) (h₃ : ∀ a b, f (a + b) ≤ max (f a) (f b)) :
    f 2009 = 1 := by
  -- First, prove that for all positive integers n, f(n) ≤ 1
  have h_pos : ∀ n : ℤ, n > 0 → f n ≤ 1 := by
    intro n hn
    induction n using Int.induction_on with
    | hz => -- Case n = 0, not used since n > 0
      linarith
    | hp n ih => -- Case n+1
      by_cases h_n_pos : (n:ℤ) > 0
      · -- If n > 0, apply the inductive hypothesis
        have : f n ≤ 1 := ih h_n_pos
        calc
          f (n + 1) ≤ max (f n) (f 1) := h₃ n 1
          _ ≤ max 1 1 := by simp [this, h₁]
          _ = 1 := by simp
      · -- If n ≤ 0, then n+1 ≤ 1
        norm_cast at h_n_pos
        have : n ≤ 0 := le_of_not_gt h_n_pos
        have : n + 1 ≤ 1 := by linarith
        cases' le_or_lt (n + 1) 0 with h_le h_gt
        · -- If n+1 ≤ 0, contradiction since n+1 > 0
          exfalso
          linarith
        · -- If 0 < n+1 ≤ 1, then n+1 must equal 1
          have : n + 1 = 1 := by
            have : n + 1 ≤ 1 := by linarith
            have : n + 1 > 0 := h_gt
            linarith
          norm_cast
          rw [this]
          apply Int.le_of_eq
          exact h₁
    | hn n ih => -- Case n-1 (not needed since we only consider positive integers)
      linarith

  -- For all nonzero integers n, f(n) ≤ 1 using the even function property
  have h_nonzero : ∀ n : ℤ, n ≠ 0 → f n ≤ 1 := by
    intro n hn
    by_cases h_pos0 : n > 0
    · -- If n > 0, apply the previous result directly
      exact h_pos n h_pos0
    · -- If n < 0 (since n ≠ 0)
      have : n < 0 := lt_of_le_of_ne (le_of_not_gt h_pos0) (hn)
      have : -n > 0 := by linarith
      have : f (-n) ≤ 1 := h_pos (-n) this
      rw [h₀] at this
      exact this

  -- Since f(2008) ≠ 1 and f(2008) ≤ 1, then f(2008) < 1
  have h_2008_lt : f 2008 < 1 := by
    have h1 : f 2008 ≤ 1 := h_pos 2008 (by norm_num)
    have h2 : f 2008 ≠ 1 := h₂
    have h3 : f 2008 < 1 := by
      apply lt_iff_le_and_ne.mpr
      constructor
      · exact h1
      · exact h2
    exact h3

  -- Since f(-2008) = f(2008) < 1 (using the even function property)
  have h_neg_2008 : f (-2008) < 1 := by
    rw [h₀]
    exact h_2008_lt

  -- Now we can prove that f(2009) = 1
  have : 1 = f 1 := h₁.symm
  have h1: f 1 = f (2009 + (-2008)) := by
    congr
  have : f (2009 + (-2008)) ≤ max (f 2009) (f (-2008)) := h₃ 2009 (-2008)

  have : 1 ≤ max (f 2009) (f (-2008)) := by
    rw[←h₁]
    rw [h1]
    exact this

  have : f 2009 = 1 := by
    have : max (f 2009) (f (-2008)) ≤ 1 := by
      apply max_le
      · -- f(2009) ≤ 1
        exact h_pos 2009 (by norm_num)
      · -- f(-2008) < 1
        linarith [h_neg_2008]

    have : max (f 2009) (f (-2008)) = 1 := by
      apply le_antisymm
      · exact this
      · exact ‹1 ≤ max (f 2009) (f (-2008))›

    have : f (-2008) < 1 := h_neg_2008
    have : f 2009 ≤ 1 := h_pos 2009 (by norm_num)

    -- If the max is 1 and f(-2008) < 1, then f(2009) must be 1
    by_contra h_contra
    have : f 2009 < 1 := by
      apply lt_of_le_of_ne this
      exact h_contra
    have : max (f 2009) (f (-2008)) < 1 := max_lt this h_neg_2008
    linarith [‹max (f 2009) (f (-2008)) = 1›]
  exact this
