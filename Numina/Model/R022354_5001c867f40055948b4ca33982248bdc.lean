import Mathlib

theorem number_theory_37227 :
    IsLeast {n : ℕ | ¬∃ x y : ℤ, n = x ^ 3 + 3 * y ^ 3} 6 := by
  constructor
  · -- Show that 6 is in the set
    show ¬∃ x y : ℤ, 6 = x ^ 3 + 3 * y ^ 3
    rintro ⟨x, y, h⟩
    have h1 : x ^ 3 + 3 * y ^ 3 = 6 := by linarith
    have h2 : x ^ 3 = 6 - 3 * y ^ 3 := by linarith
    have h3 : x^3 % 3 = 0 := by
      omega
    have h4 : x % 3 = 0 := by
      have h5 : x ^ 3 % 3 = 0 := by
        omega
      have h6 : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by 
        omega
      rcases h6 with (h | h | h) <;> 
        norm_num [pow_succ, Int.add_emod, Int.mul_emod, h, Int.sub_emod] at h5 <;> tauto
    have h7 : ∃ k : ℤ, x = 3 * k := by 
      refine' ⟨x / 3, by 
        omega⟩
    rcases h7 with ⟨k, hk⟩
    rw [hk] at h1
    have h8 : 9 * k ^ 3 + y ^ 3 = 2 := by 
      nlinarith 
    have h9 : y ^ 3 % 9 = 0 ∨ y ^ 3 % 9 = 1 ∨ y ^ 3 % 9 = 8 := by
      have h10 : y % 9 = 0 ∨ y % 9 = 1 ∨ y % 9 = 2 ∨ y % 9 = 3 ∨ y % 9 = 4 ∨ y % 9 = 5 ∨ y % 9 = 6 ∨ y % 9 = 7 ∨ y % 9 = 8 := by
        omega 
      rcases h10 with (h | h | h | h | h | h | h | h | h) <;> 
        norm_num [pow_succ, Int.add_emod, Int.mul_emod, h, Int.sub_emod] 
    have h10 : y ^ 3 % 9 = 2 := by
      have h11 : (9 * k ^ 3 + y ^ 3) % 9 = 2 % 9 := by
        omega
      have h12 : (9 * k ^ 3) % 9 = 0 := by
        ring_nf
        <;> omega 
      omega 
    omega 
  · -- Show that 6 is the least in the set
    intro n hn
    have h1 : n ∈ {n : ℕ | ¬∃ x y : ℤ, n = x ^ 3 + 3 * y ^ 3} := by
      simpa using hn
    have h2 : ¬∃ x y : ℤ, n = x ^ 3 + 3 * y ^ 3 := by 
      simpa using h1 
    by_contra h3
    push_neg at h3
    have h4 : n < 6 := h3
    have : ∃ x y : ℤ, n = x ^ 3 + 3 * y ^ 3 := by 
      have h5 : n < 6 := h4
      have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by 
        omega
      rcases this with (r | r | r | r | r | r) <;> 
        ( 
          try { 
            rw [show (n : ℕ) = (0 : ℕ) by omega] 
            use 0, 0 
            all_goals norm_num 
          } 
        ) <;> 
          ( 
            try { 
              rw [show (n : ℕ) = (1 : ℕ) by omega] 
              use 1, 0 
              all_goals norm_num 
            } 
          ) <;> 
            ( 
              try { 
                rw [show (n : ℕ) = (2 : ℕ) by omega] 
                use -1, 1 
                all_goals norm_num 
              } 
            ) <;> 
              ( 
                try { 
                  rw [show (n : ℕ) = (3 : ℕ) by omega] 
                  use 0, 1 
                  all_goals norm_num 
                } 
              ) <;> 
                ( 
                  try { 
                    rw [show (n : ℕ) = (4 : ℕ) by omega] 
                    use 1, 1 
                    all_goals norm_num 
                  } 
                ) <;> 
                  ( 
                    try { 
                      rw [show (n : ℕ) = (5 : ℕ) by omega] 
                      use 2, -1 
                      all_goals norm_num 
                    } 
                  )
    contradiction