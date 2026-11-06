import Mathlib

theorem algebra_302850 {k : ℤ} (h : ∃ x1 x2 : ℕ, x1 > 0 ∧ x2 > 0 ∧ x1 ≠ x2 ∧ (k^2 - 1)*x1^2 - 3*(3*k - 1)*x1 + 18 = 0 ∧ (k^2 - 1)*x2^2 - 3*(3*k - 1)*x2 + 18 = 0) :
    k = 2 := by
  rcases h with ⟨x1, x2, hx1, hx2, hneq, h1, h2⟩
  have h1' : (k^2 - 1)*(x1 : ℤ)^2 - 3*(3*k - 1)*(x1 : ℤ) + 18 = 0 := by
    norm_num
    omega
  have h2' : (k^2 - 1)*(x2 : ℤ)^2 - 3*(3*k - 1)*(x2 : ℤ) + 18 = 0 := by 
    norm_num
    omega
  have h3 : (k^2 - 1) * ((x1 : ℤ) + (x2 : ℤ)) = 3 * (3 * k - 1) := by
    have h4 : (k^2 - 1) * ((x1 : ℤ)^2 - (x2 : ℤ)^2) - 3 * (3 * k - 1) * ((x1 : ℤ) - (x2 : ℤ)) = 0 := by
      nlinarith 
    have h5 : (x1 : ℤ) - (x2 : ℤ) ≠ 0 := by 
      have h6 : (x1 : ℤ) > 0 := by exact_mod_cast hx1 
      have h7 : (x2 : ℤ) > 0 := by exact_mod_cast hx2 
      have h8 : (x1 : ℤ) ≠ (x2 : ℤ) := by 
        intro h
        have h9 : x1 = x2 := by 
          exact_mod_cast h 
        contradiction 
      have h5' : (x1 : ℤ) - (x2 : ℤ) ≠ 0 := by 
        intro h
        have h9 : (x1 : ℤ) = (x2 : ℤ) := by 
          linarith 
        contradiction 
      exact h5' 
    have h6 : (k^2 - 1) * ((x1 : ℤ) + (x2 : ℤ)) - 3 * (3 * k - 1) = 0 := by 
      apply (mul_left_inj' h5).mp 
      linarith 
    linarith 
  have h4 : (k : ℤ) ^ 2 - 1 ≠ 0 := by
    by_contra h5 
    have h6 : (k : ℤ) ^ 2 = 1 := by linarith 
    have h7 : k = 1 ∨ k = -1 := by 
      rw [sq_eq_one_iff] at h6 
      exact h6 
    rcases h7 with (h8 | h8)
    · -- k = 1
      have h9 : k = 1 := h8
      rw [h9] at h1' h2' 
      have eq1 : (x1 : ℤ) = 3 := by 
        nlinarith
      have eq2 : (x2 : ℤ) = 3 := by 
        nlinarith
      have h10 : (x1 : ℤ) = (x2 : ℤ) := by 
        linarith [eq1, eq2] 
      have h11 : x1 = x2 := by 
        exact_mod_cast h10 
      contradiction 
    · -- k = -1
      have h10 : k = -1 := by linarith 
      rw [h10] at h1' h2' 
      have h11 : (x1 : ℤ) > 0 := by exact_mod_cast hx1 
      have h12 : (x2 : ℤ) > 0 := by exact_mod_cast hx2 
      nlinarith 
  have h9 : (k - 2 : ℤ) = 0 := by 
    have h5 : (x1 : ℤ) > 0 := by exact_mod_cast hx1 
    have h6 : (x2 : ℤ) > 0 := by exact_mod_cast hx2 
    have h7 : (k^2 - 1 : ℤ) ≠ 0 := h4 
    nlinarith [sq_nonneg ((x1 : ℤ) - (x2 : ℤ)), sq_nonneg ((k : ℤ) - 2), sq_nonneg ((k : ℤ) + 1), sq_nonneg ((k : ℤ) - 1)
      , sq_pos_of_ne_zero (show (k^2 - 1 : ℤ) ≠ 0 by exact_mod_cast h4), sq_pos_of_ne_zero (show (x1 : ℤ) - (x2 : ℤ) ≠ 0 by 
        have h9 : (x1 : ℤ) > 0 := by exact_mod_cast hx1 
        have h10 : (x2 : ℤ) > 0 := by exact_mod_cast hx2 
        have h11 : (x1 : ℤ) ≠ (x2 : ℤ) := by 
          intro h
          have h12 : x1 = x2 := by 
            exact_mod_cast h 
          contradiction 
        intro h
        have h13 : (x1 : ℤ) = (x2 : ℤ) := by 
          linarith 
        contradiction 
      ) 
    ] 
  linarith