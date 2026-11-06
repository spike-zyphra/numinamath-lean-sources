import Mathlib

theorem algebra_170298 (f : ℝ → ℝ) (h₀ : ∀ x y, x < y → f x > f y) (h₁ : Function.Odd f) :
    {r : ℝ | ∃m n : ℝ, f m + f (n - 2) ≤ 0 ∧ f (m - n - 1) ≤ 0 ∧ r = 5 * m - n} = 
    Set.Ici 7 := by
  ext r
  simp only [Set.mem_setOf_eq, Set.mem_Ici]
  constructor
  · -- First direction: If r exists as 5m - n with constraints
    rintro ⟨m, n, h2, h3, h4⟩
    have h41 : m - n - 1 ≥ 0 := by
      by_contra h
      push_neg at h
      have h5 : f (m - n - 1) > f 0 := by
        apply h₀
        linarith
      have h51 : f 0 = 0 := by
        have : f 0 = 0 := by
          have h1 := h₁ 0
          simp at h1
          linarith 
        linarith 
      linarith 
    have h42 : m + n ≥ 2 := by
      have h5 : f m ≤ f (2 - n) := by
        have h6 : f m + f (n - 2) ≤ 0 := h2
        have h7 : f (n - 2) = -f (2 - n) := by
          have : f (2 - n) = -f (n - 2) := by
            have h8 : 2 - n = - (n - 2) := by ring 
            rw [h8] 
            have h9 : f (- (n - 2)) = - f (n - 2) := by
              apply h₁ 
            linarith 
          linarith 
        linarith 
      have h8 : m ≥ 2 - n := by
        by_contra h
        push_neg at h
        have h9 : f m > f (2 - n) := by
          apply h₀
          linarith 
        linarith [h5, h9] 
      linarith 
    nlinarith 
  · -- Second direction: from r ≥ 7 to existence of m, n satisfying the constraints
    intro hr
    use (r + 2) / 6, 2 - (r + 2) / 6
    constructor
    · -- Show that $f(m) + f(n - 2) \leq 0$
      have h6 : (r + 2 : ℝ) / 6 ≥ (3 / 2 : ℝ) := by
        nlinarith 
      have h9 : f ((r + 2 : ℝ) / 6) + f (2 - (r + 2 : ℝ) / 6 - 2) = 0 := by
        have h15 : f (2 - (r + 2 : ℝ) / 6 - 2) = -f ((r + 2 : ℝ) / 6) := by
          have h18 : 2 - (r + 2 : ℝ) / 6 - 2 = - ((r + 2 : ℝ) / 6) := by
            ring_nf 
          rw [h18] 
          have h19 : f (- ((r + 2 : ℝ) / 6)) = - f ((r + 2 : ℝ) / 6) := by
            apply h₁ 
          linarith [h19]
        linarith [h15]
      linarith [h9]
    constructor
    · -- Show that $f(m - n - 1) \leq 0$
      have h12 : ((r + 2 : ℝ) / 6 - (2 - (r + 2 : ℝ) / 6) - 1) = (r - 7) / 3 := by
        ring_nf 
      have h5 : f ((r + 2 : ℝ) / 6 - (2 - (r + 2 : ℝ) / 6) - 1 : ℝ) ≤ (0 : ℝ) := by
        rw [h12]
        by_cases h : r > 7
        · -- If r > 7, then (r - 7) / 3 > 0. Since f is decreasing, f((r - 7) / 3) < f(0) = 0.
          have h7 : (0 : ℝ) < ((r - 7) / 3 : ℝ) := by
            linarith 
          have h9 : f (0 : ℝ) > f ((r - 7) / 3 : ℝ) := by
            apply h₀ 
            all_goals 
              nlinarith [h7, hr] 
          have h10 : f (0 : ℝ) = 0 := by
            have h16 : f (0 : ℝ) = 0 := by
              have h17 : f (- (0 : ℝ)) = - f (0 : ℝ) := by
                apply h₁ 
              simp at h17 
              linarith [h17]
            linarith 
          linarith 
        · -- If r = 7
          have h7 : r = 7 := by
            linarith 
          rw [h7] 
          norm_num 
          all_goals 
            try { 
              have h8 : f (0 : ℝ) = 0 := by
                have h16 : f (0 : ℝ) = 0 := by
                  have h17 : f (- (0 : ℝ)) = - f (0 : ℝ) := by
                    apply h₁ 
                  simp at h17 
                  linarith [h17]
                linarith 
              linarith [h8] 
            }
          all_goals 
            try { linarith [hr] }
      linarith [h5]
    · -- Show that r = 5 * m - n
      linarith