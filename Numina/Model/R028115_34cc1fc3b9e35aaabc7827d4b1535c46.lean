import Mathlib

theorem algebra_321710
    (x y z : ℕ)
    (h₀ : 0 < x)
    (h₁ : 0 < y)
    (h₂ : 0 < z)
    (h₃ : x^2 + y^2 + z^2 = 2 * (y * z + 1))
    (h₄ : x + y + z = 4032) :
    x^2 * y + z = 4031 := by
  have h5 : x = 1 := by
    have h6 : x ≤ 1 := by
      nlinarith [sq_nonneg (x : ℕ), sq_nonneg ((y : ℕ) - (z : ℕ)), sq_nonneg ((z : ℕ) - (y : ℕ)), sq_nonneg ((y * (z): ℤ)), sq_nonneg ((z * (y): ℤ)), sq_nonneg (y - z : ℤ), sq_nonneg (z - y : ℤ)]
    have h7 : x ≥ 1 := by
      linarith 
    have hx : x = 1 := by 
      linarith 
    exact hx
  have h8 : x = 1 := h5
  have h9 : y + z = 4031 := by 
    nlinarith [h₄, h8]
  have h12 : ((y : ℤ) - (z : ℤ)) ^ 2 = 1 := by
    have h13 : (x : ℤ) = 1 := by 
      exact_mod_cast h8 
    have h14 : (x : ℤ) ^ 2 + (y : ℤ) ^ 2 + (z : ℤ) ^ 2 = 2 * ((y : ℤ) * (z : ℤ) + 1) := by 
      exact_mod_cast h₃
    rw [h13] at h14
    nlinarith [sq_nonneg ((y : ℤ) - (z : ℤ)), sq_nonneg ((y : ℤ) + (z : ℤ)), sq_nonneg (y - z : ℤ), sq_nonneg (z - y : ℤ)]
  have h13 : (y : ℤ) - (z : ℤ) = 1 ∨ (y : ℤ) - (z : ℤ) = -1 := by 
    rw [sq_eq_one_iff] at h12 
    simpa using h12 
  rcases h13 with h | h 
  · -- Assume (y : ℤ) - (z : ℤ) = 1 
    have h14 : (y : ℤ) = (z : ℤ) + 1 := by 
      linarith 
    have h15 : y = z + 1 := by 
      omega 
    have h16 : z = 2015 := by 
      nlinarith [h9, h15]
    have h17 : y = 2016 := by 
      nlinarith [h9, h16]
    calc 
      x^2 * y + z = 1 ^ 2 * 2016 + 2015 := by 
        rw [show x = 1 by linarith, h17, h16]
      _ = 1 * 2016 + 2015 := by 
        norm_num 
      _ = 2016 + 2015 := by 
        norm_num 
      _ = 4031 := by 
        norm_num 
  · -- Assume (y : ℤ) - (z : ℤ) = -1 
    have h18 : (z : ℤ) = (y : ℤ) + 1 := by 
      linarith 
    have h19 : z = y + 1 := by 
      omega 
    have h20 : y = 2015 := by 
      nlinarith [h9, h19]
    have h21 : z = 2016 := by 
      omega 
    calc 
      x^2 * y + z = 1 ^ 2 * 2015 + 2016 := by 
        rw [show x = 1 by linarith, h20, h21]
      _ = 1 * 2015 + 2016 := by 
        norm_num 
      _ = 2015 + 2016 := by 
        norm_num 
      _ = 4031 := by 
        norm_num