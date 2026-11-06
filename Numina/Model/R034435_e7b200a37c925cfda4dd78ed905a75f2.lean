import Mathlib

theorem algebra_235729 {a : ℕ → ℝ} {d : ℝ} (h : ∀ n, a n = a 0 + d * n)
    (h' : d < 0) (S : ℕ → ℝ) (hS : ∀ n, S n = ∑ i in Finset.range n, a i) :
    ∀ n, n * a n ≤ S n ∧ S n ≤ n * a 0 := by
  intro n
  have h1 : ∀ (n : ℕ), S n = n * a 0 + d * (n * (n - 1 : ℝ) / 2 : ℝ) := by
    intro n 
    rw [hS n]
    induction n with
    | zero =>
      simp 
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp [h n]
      <;> ring 
  have h2 : S n = n * a 0 + d * (n * (n - 1 : ℝ) / 2 : ℝ) := h1 n 
  have h3 : a n = a 0 + d * (n : ℝ) := by
    specialize h n 
    simpa using h 
  constructor 
  · -- Show n * a n ≤ S n 
    rw [h2, h3]
    have h4 : (n : ℝ) * (a 0 + d * (n : ℝ)) ≤ (n : ℝ) * a 0 + d * ((n : ℝ) * ((n : ℝ) - 1) / 2 : ℝ) := by 
      have h5 : d < (0 : ℝ) := h'
      have h7 : ( (n : ℝ) ^ 2 ) ≥ ( (n : ℝ) * ((n : ℝ) - 1) / 2 ) := by
        have hn1 : (n : ℝ) ≥ (0 : ℝ) := by positivity 
        have h8 : (n : ℝ) * ((n : ℝ) - 1) ≥ - n := by
          have hn0 : (n : ℝ) ≥ 0 := by positivity 
          by_cases h9 : (n : ℝ) ≥ (1 : ℝ)
          · 
            nlinarith 
          · 
            nlinarith [show (n : ℝ) ≤ (1 : ℝ) by linarith]
        nlinarith [sq_nonneg ((n : ℝ) - 1), sq_nonneg ((n : ℝ))]
      have h6 : ((n : ℝ) * (n : ℝ)) * d ≤ d * ( (n : ℝ) * ((n : ℝ) - 1) / 2 : ℝ) := by
        have h9 : d < (0 : ℝ) := h'
        nlinarith [show (n : ℝ) * ((n : ℝ) - 1) / 2 ≤ (n : ℝ) * (n : ℝ) by linarith [sq_nonneg ((n : ℝ) - 1), sq_nonneg ((n : ℝ))], h']
      have h10 : (n : ℝ) * (a 0 + d * (n : ℝ)) = (n : ℝ) * a 0 + ((n : ℝ) * (n : ℝ)) * d := by 
        ring_nf
      linarith [h10, h6]
    linarith 
  · -- Show S n ≤ n * a 0 
    rw [h2]
    have h6 : d < (0 : ℝ) := h'
    have h7 : d * ((n : ℝ) * ((n : ℝ) - 1) / 2 : ℝ) ≤ 0 := by
      have h8 : ((n : ℝ) * ((n : ℝ) - 1) / 2 : ℝ) ≥ 0 := by
        have hn1 : (n : ℝ) ≥ 0 := by positivity
        have h9 : (n : ℝ) * ((n : ℝ) - 1) / 2 ≥ 0 := by 
          by_cases h10 : (n : ℝ) ≥ (1 : ℝ)
          · 
            have hn2 : (n : ℝ) ≥ 1 := h10 
            have hn5 : (n : ℝ) * ((n : ℝ) - 1) ≥ 0 := by 
              have h11 : (n : ℝ) ≥ 1 := hn2 
              nlinarith [sq_nonneg ((n : ℝ) - 1)]
            have : (n : ℝ) * ((n : ℝ) - 1) / 2 ≥ 0 := by 
              apply div_nonneg 
              linarith 
              all_goals norm_num 
            linarith 
          · 
            have h11 : (n : ℝ) < (1 : ℝ) := by linarith
            have hn3 : (n : ℝ) = (0 : ℝ) := by 
              have h12 : (n : ℝ) < (1 : ℝ) := by linarith 
              have hn4 : (n : ℝ) ≥ (0 : ℝ) := by positivity 
              have hn5 : (n : ℝ) = (0 : ℝ) := by
                have h100 : (n : ℕ) = 0 := by 
                  have hn6 : (n : ℝ) < (1 : ℝ) := by linarith 
                  have hn7 : (n : ℝ) ≥ (0 : ℝ) := hn4 
                  have hn8 : (n : ℕ) < (1 : ℕ) := by 
                    by_contra h 
                    push_neg at h 
                    have : (n : ℕ) ≥ (1 : ℕ) := by 
                      omega 
                    have h100 : (n : ℝ) ≥ (1 : ℝ) := by 
                      exact_mod_cast this 
                    linarith 
                  have hn9 : (n : ℕ) = 0 := by 
                    omega 
                  exact_mod_cast hn9 
                exact_mod_cast h100 
              linarith 
            rw [hn3]
            norm_num 
        linarith 
      nlinarith [h']
    nlinarith