import Mathlib

theorem algebra_169157 (x : ℝ) : Real.cos (2 * x) + Real.cos (3 * x / 4) - 2 = 0 ↔
    ∃ n : ℤ, x = 8 * Real.pi * n := by 
  constructor
  · -- First direction: equation to solutions
    intro h
    have h1 : Real.cos (2 * x) = 1 := by 
      nlinarith [Real.cos_le_one (2 * x), Real.cos_le_one (3 * x / 4), 
        Real.neg_one_le_cos (2 * x), Real.neg_one_le_cos (3 * x / 4)]
    have h2 : Real.cos (3 * x / 4) = 1 := by 
      nlinarith [Real.cos_le_one (2 * x), Real.cos_le_one (3 * x / 4), 
        Real.neg_one_le_cos (2 * x), Real.neg_one_le_cos (3 * x / 4)]
    
    have h3 : ∃ k : ℤ, 2 * x = 2 * Real.pi * k := by
      have h3 : Real.cos (2 * x) = 1 := h1
      have h4 : ∃ k : ℤ, 2 * x = 2 * Real.pi * k := by
        rw [Real.cos_eq_one_iff] at h3
        rcases h3 with ⟨k, hk⟩
        use k
        all_goals linarith
      exact h4
    rcases h3 with ⟨k, hk⟩
    
    have h4 : ∃ m : ℤ, 3 * x / 4 = 2 * Real.pi * m := by
      have h4 : Real.cos (3 * x / 4) = 1 := h2
      have h5 : ∃ m : ℤ, 3 * x / 4 = 2 * Real.pi * m := by
        rw [Real.cos_eq_one_iff] at h4 
        rcases h4 with ⟨m, hm⟩
        use m
        all_goals linarith
      exact h5
    rcases h4 with ⟨m, hm⟩

    have hx_eq : x = Real.pi * (k : ℝ) := by
      calc
        x = (2 * x) / 2 := by ring
        _ = (2 * Real.pi * (k : ℝ)) / 2 := by rw [hk]
        _ = Real.pi * (k : ℝ) := by ring

    have eq1 : 3 * (k : ℝ) / 8 = (m : ℝ) := by
      rw [hx_eq] at hm
      have h5 : 3 * (Real.pi * (k : ℝ)) / 4 = 2 * Real.pi * (m : ℝ) := hm 
      have h7 : Real.pi ≠ 0 := Real.pi_ne_zero
      have eq3 : (3 * (k : ℝ) ) / 8 = (m : ℝ) := by
        nlinarith [Real.pi_pos]
      linarith

    have eq3 : 3 * k = 8 * m := by
      have eq4 : (3 * (k : ℝ) ) / 8 = (m : ℝ) := eq1
      have eq5 : (3 * k : ℝ) = 8 * (m : ℝ) := by
        linarith [eq4]
      have eq6 : (3 * k : ℝ) = (8 * m : ℝ) := by
        linarith [eq5]
      have eq7 : (3 * k : ℤ) = (8 * m : ℤ) := by
        exact_mod_cast eq6 
      norm_cast at eq7 
      <;> omega

    -- Now we need to show that k is multiple of 8 from 3k=8m
    have h5 : k % 8 = 0 := by
      omega

    have h6 : ∃ n : ℤ, k = 8 * n := by 
      refine' ⟨k / 8, by omega⟩ 
    rcases h6 with ⟨n, hn⟩ 
    use n 
    rw [hx_eq]
    rw [hn]
    all_goals 
      ring_nf 
      <;> norm_num 
      <;> linarith
  
  · -- Second direction: solutions to equation
    rintro ⟨n, hn⟩
    have h1 : Real.cos (2 * x) = 1 := by
      rw [show 2 * x = 16 * (n : ℝ) * Real.pi by
        rw [hn]
        ring_nf 
      ]
      have h2 : 16 * (n : ℝ) * Real.pi = (8 * (n : ℝ)) * (2 * Real.pi) := by ring
      rw [h2]
      have h3 : Real.cos ((8 * (n : ℝ)) * (2 * Real.pi)) = 1 := by 
        have h4 : Real.cos ((8 * (n : ℝ)) * (2 * Real.pi)) = Real.cos (↑(8 * n : ℤ) * (2 * Real.pi)) := by 
          norm_cast 
        rw [h4]
        have h7 : Real.cos (↑(8 * n : ℤ) * (2 * Real.pi)) = 1 := by 
          have h10 : Real.cos (↑(8 * n : ℤ) * (2 * Real.pi)) = 1 := by 
            rw [Real.cos_int_mul_two_pi (8 * n)]
          exact h10 
        exact h7 
      exact h3
    have h4 : Real.cos (3 * x / 4) = 1 := by
      rw [show 3 * x / 4 = 6 * (n : ℝ) * Real.pi by 
        rw [hn]
        ring_nf 
      ]
      have h8 : 6 * (n : ℝ) * Real.pi = (3 * (n : ℝ)) * (2 * Real.pi) := by ring
      rw [h8]
      have h9 : Real.cos ((3 * (n : ℝ)) * (2 * Real.pi)) = 1 := by 
        have h10 : Real.cos ((3 * (n : ℝ)) * (2 * Real.pi)) = Real.cos (↑(3 * n : ℤ) * (2 * Real.pi)) := by 
          norm_cast 
        rw [h10]
        have h11 : Real.cos (↑(3 * n : ℤ) * (2 * Real.pi)) = 1 := by
          have h12 : Real.cos (↑(3 * n : ℤ) * (2 * Real.pi)) = 1 := by 
            rw [Real.cos_int_mul_two_pi (3 * n)]
          exact h12 
        exact h11 
      exact h9 
    linarith [h1, h4]