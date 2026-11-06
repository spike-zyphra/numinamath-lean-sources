import Mathlib

theorem algebra_274101 {m n p : ℤ} (hm : m > 0) (hn : n > 0) (hp : p > 0)
    (h : m + 1 / (n + 1 / p : ℝ) = 17 / 3) : n = 1 := by
  have h1 : (m : ℝ) > 0 := by exact_mod_cast hm
  have h2 : (n : ℝ) > 0 := by exact_mod_cast hn
  have h3 : (p : ℝ) > 0 := by exact_mod_cast hp
  have eq1 : (m : ℝ) + 1 / (n + 1 / p : ℝ) = 17 / 3 := by linarith

  have h4 : (m : ℝ) < 17 / 3 := by
    have h5 : 1 / (n + 1 / p : ℝ) > 0 := by
      apply div_pos
      norm_num
      positivity
    nlinarith

  have h6 : (m : ℝ) > 14 / 3 := by
    have h7 : 1 / (n + 1 / p : ℝ) < 1 := by
      have h8 : (n + 1 / p : ℝ) > 1 := by
        have hn1 : n >= 1 := by omega
        have hp1 : p >= 1 := by omega
        have hn2 : (n : ℝ) >= (1 : ℝ) := by exact_mod_cast hn1
        have hp2 : (p : ℝ) >= (1 : ℝ) := by exact_mod_cast hp1
        have hp1' : (1/p : ℝ) > 0 := by positivity
        have h11 : (1/p : ℝ) >= 0 := by linarith
        have h12 : (n + 1/p : ℝ) >= (1 : ℝ) := by linarith [hn2, h11]
        -- Now prove that (n + 1/p : ℝ) > 1
        by_contra h13
        push_neg at h13
        have h14 : (n + 1/p : ℝ) ≤ (1 : ℝ) := by linarith
        have hn1' : n >= 1 := by omega
        have hp1' : p >= 1 := by omega
        have hn2' : (n : ℝ) >= (1 : ℝ) := by exact_mod_cast hn1'
        have hp2' : (p : ℝ) >= (1 : ℝ) := by exact_mod_cast hp1'
        have hp1' : (1/p : ℝ) > 0 := by positivity
        have h15 : (p : ℝ) >= 1 := by linarith [hp2']
        have h16 : (1 / p : ℝ) <= (1 : ℝ) := by
          have h17 : (1 / (p : ℝ) : ℝ) <= (1 / 1 : ℝ) := by
            apply (div_le_div_iff (by positivity) (by norm_num)).mpr
            nlinarith
          norm_num at h17 ⊢
          linarith
        nlinarith
      -- Prove 1/((n + 1/p) < 1
      have h9 : (1 / (n + 1 / p : ℝ) : ℝ) < (1 : ℝ) := by
        apply (div_lt_iff₀ (by positivity)).mpr
        nlinarith
      norm_num at h9 ⊢
      linarith
    -- Prove m > 14/3
    have h8 : 1 / (n + 1 / p : ℝ) > 0 := by 
      apply div_pos
      norm_num
      positivity
    nlinarith [h8, h7]
  
  -- Now with bounds, we can infer m = 5
  have h7 : m = 5 := by
    have h14 : m < 6 := by
      by_contra h15
      push_neg at h15
      have h16 : m >= 6 := by omega
      have h17 : (m : ℝ) >= (6 : ℝ) := by exact_mod_cast h16
      nlinarith
  
    have h15 : m >= 5 := by
      by_contra h16
      push_neg at h16
      have h17 : m <= 4 := by omega
      have h18 : (m : ℝ) <= (4 : ℝ) := by exact_mod_cast h17
      nlinarith
  
    omega
  rw [show (m : ℝ) = 5 by exact_mod_cast h7] at eq1
  have eq2 : 1 / (n + 1 / p : ℝ) = 2 / 3 := by linarith
  have eq3 : (n + 1 / p : ℝ) = 3 / 2 := by
    field_simp at eq2 ⊢
    nlinarith

  have hn1 : (n : ℝ) < (3 / 2 : ℝ) := by
    have hp1 : (1 / p : ℝ) > 0 := by positivity
    nlinarith
  
  have h8 : n = 1 := by
    have hn2 : n < 2 := by
      by_contra h15
      push_neg at h15
      have hn3 : n >= 2 := by omega
      have hn4 : (n : ℝ) >= (2 : ℝ) := by exact_mod_cast hn3
      nlinarith -- contradiction with hn1
    interval_cases n <;> try { tauto }
  -- Final assertion that n = 1 is the only solution
  exact h8