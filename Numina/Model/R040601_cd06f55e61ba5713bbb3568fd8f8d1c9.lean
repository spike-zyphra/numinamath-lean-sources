import Mathlib

theorem algebra_300593 {a : ℕ → ℝ} (h : ∀ n, (3 - a (n + 1)) * (6 + a n) = 18) (ha : a 0 = 3) :
    ∑ i in Finset.range (n + 1), 1 / a i = (2 ^ (n + 2) - n - 3) / 3 := by
  have h1 : ∀ n, a n ≠ 0 := by
    intro n
    have h2 : ∀ n : ℕ, a n ≠ 0 := by
      intro n
      induction n with
      | zero =>
        rw [ha]
        norm_num 
      | succ n ih =>
        by_contra h3 
        have h4 : a (n + 1) = 0 := by linarith 
        have h5 : (3 - a (n + 1)) * (6 + a n) = 18 := h (n )
        rw [show a (n + 1) = (0 : ℝ) by linarith [h4]] at h5 
        have h6 : a n ≠ 0 := ih 
        have h7 : (6 + a n) = 6 := by 
          have h8 : (3 - (0 : ℝ)) * (6 + a n) = 18 := by 
            simpa using h5 
          have h9 : (3 ) * (6 + a n) = 18 := by 
            nlinarith [h8] 
          linarith 
        have h8 : a n = (0 : ℝ) := by 
          linarith 
        contradiction
    simpa using h2 n
  have h2' : ∀ n : ℕ, 1 / a n = (2 ^ (n + 1) - 1) / 3 := by
    intro n 
    induction n with 
    | zero =>
      rw [ha] 
      norm_num 
    | succ n ih =>
      have h3 : a n ≠ 0 := h1 n 
      have h4 : a (n + 1) ≠ 0 := h1 (n + 1) 
      have eq1 : (3 - a (n + 1)) * (6 + a n) = 18 := h n 
      have eq2 : 1 / a n = (2 ^ (n + 1) - 1) / 3 := ih 
      have eq3 : 1 / a (n + 1) = 2 * (1 / a n) + 1 / 3 := by 
        field_simp [show a n ≠ 0 by exact h3, show a (n + 1) ≠ 0 by exact h4] at *
        nlinarith [eq1] 
      rw [eq3, eq2] 
      field_simp 
      ring_nf 
  have h3 : ∀ (n : ℕ), ∑ i in Finset.range (n + 1), 1 / a i = (2 ^ (n + 2) - n - 3) / 3 := by 
    intro n 
    induction n with 
    | zero =>
      simp [h2']
      all_goals norm_num 
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp [h2']
      all_goals field_simp at *
      all_goals ring_nf 
      all_goals norm_num
      all_goals ring_nf 
  specialize h3 n 
  simpa using h3