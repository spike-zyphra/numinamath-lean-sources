import Mathlib

theorem number_theory_205763 :
  {(x, y) : ℤ × ℤ | (x + 2)^4 - x^4 = y^3} = {(-1, 0)} := by 
  ext ⟨x, y⟩
  simp 
  constructor 
  · -- Assume (x + 2)^4 - x^4 = y^3, we need to prove (x, y) = (-1, 0)
    intro h_eq 
    have h1 : (x + 2)^4 - x^4 = y^3 := h_eq 
    have h2 : y ^ 3 = 8 * (x ^ 3 + 3 * x ^ 2 + 4 * x + 2) := by 
      nlinarith [h1]

    have h3 : y % 2 = 0 := by 
      by_contra h4
      push_neg at h4
      have h4' : y % 2 = 1 := by 
        omega 
      have h5 : y ^ 3 % 8 = 1 ∨ y ^ 3 % 8 = 3 ∨ y ^ 3 % 8 = 5 ∨ y ^ 3 % 8 = 7 := by 
        have h6 : y % 2 = 1 := h4'
        have : y % 8 = 1 ∨ y % 8 = 3 ∨ y % 8 = 5 ∨ y % 8 = 7 := by 
          omega 
        rcases this with (h | h | h | h) <;> simp [h, pow_succ, Int.add_emod, Int.mul_emod] 
      have h5' : y ^ 3 % 8 = 0 := by
        omega 
      omega

    have h4' : ∃ k, y = 2 * k := by 
      refine' ⟨y / 2, by omega⟩

    rcases h4' with ⟨k, hyk⟩
    have h5 : (2 * k) ^ 3 = 8 * (x ^ 3 + 3 * x ^ 2 + 4 * x + 2) := by 
      rw [show y = 2 * k by linarith [hyk]] at h2 
      all_goals linarith [h2]
    have h6 : k ^ 3 = x ^ 3 + 3 * x ^ 2 + 4 * x + 2 := by 
      nlinarith [h5]
    have h7 : k ^ 3 = (x + 1) ^ 3 + (x + 1) := by 
      nlinarith [h6]

    have h8 : k = x + 1 := by
      by_cases h8' : k > x + 1 
      · -- Assume k > x + 1, then get a contradiction 
        have h9 : k ^ 3 > (x + 1) ^ 3 := by 
          nlinarith [sq_nonneg ((k : ℤ) - (x + 1) : ℤ), sq_nonneg ((k + (x + 1) : ℤ)), sq_pos_of_pos (show k - (x + 1) > 0 by linarith)]
        nlinarith [sq_nonneg ((k : ℤ) - (x + 1) : ℤ), sq_nonneg ((k + (x + 1)) : ℤ), sq_nonneg ((k ^ 2 - (x + 1) ^ 2) : ℤ)]
      · 
        by_cases h9' : k < x + 1 
        · -- Assume k < x + 1, then get a contradiction 
          have h10 : k ^ 3 < (x + 1) ^ 3 := by 
            nlinarith [sq_nonneg ((k : ℤ) - (x + 1) : ℤ), sq_nonneg ((k + (x + 1) : ℤ)), sq_pos_of_pos (show (x + 1) - k > 0 by linarith)]
          nlinarith [sq_nonneg ((k : ℤ) - (x + 1) : ℤ), sq_nonneg ((k + (x + 1)) : ℤ), sq_nonneg ((k ^ 2 - (x + 1) ^ 2) : ℤ)]
        · -- k = x + 1 
          have h11 : k ≥ x + 1 := by 
            omega 
          have h12 : k ≤ x + 1 := by 
            omega 
          have h13 : k = x + 1 := by 
            linarith 
          assumption

    -- From k = x + 1 and h6: k^3 = ..., we can find x.
    have eq1 : x = -1 := by 
      rw [show k = x + 1 by linarith [h8]] at h7 
      ring_nf at h7 
      have h9 : x = -1 := by 
        nlinarith [sq_nonneg (x + 1 : ℤ), sq_nonneg ((x ^ 2 + 3 * x + 3) : ℤ)]
      assumption

    -- Then y = 0.
    have eq2 : y = 0 := by 
      linarith [hyk, eq1, h8] 

    simp [eq1, eq2]

  · -- Show that $(-1, 0)$ is in the left-hand side set.
    rintro ⟨rfl, rfl⟩ 
    norm_num