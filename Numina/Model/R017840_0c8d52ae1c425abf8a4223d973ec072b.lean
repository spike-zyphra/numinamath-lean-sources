import Mathlib


open Set


theorem algebra_177354 (k : ℤ) (h : ∃ x y z, x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
    (x^3 - x + k = 0 ∧ y^3 - y + k = 0 ∧ z^3 - z + k = 0)) :
    k = 0 := by
  rcases h with ⟨x, y, z, hxy, hyz, hzx, ⟨hx, hy, hz⟩⟩

  have h1 : (x - y) * (x^2 + x * y + y^2 - 1) = 0 := by
    nlinarith 
  have h2 : x^2 + x * y + y^2 = 1 := by
    apply (mul_left_inj' (show (x - y : ℤ) ≠ 0 by 
      intro h'
      apply hxy
      linarith 
    )).mp
    linarith

  have h3 : (y - z) * (y^2 + y * z + z^2 - 1) = 0 := by
    nlinarith 
  have h4 : y^2 + y * z + z^2 = 1 := by
    apply (mul_left_inj' (show (y - z : ℤ) ≠ 0 by
      intro h'
      apply hyz
      linarith
    )).mp
    linarith
  
  have h5 : (z - x) * (z^2 + z * x + x^2 - 1) = 0 := by
    nlinarith
  have h6 : z^2 + z * x + x^2 = 1 := by
    apply (mul_left_inj' (show (z - x : ℤ) ≠ 0 by
      intro h'
      apply hzx
      linarith 
    )).mp 
    linarith

  have h8 : (x - z) * (x + y + z) = 0 := by
    nlinarith
  
  have h9 : x + y + z = 0 := by
    cases' (mul_eq_zero.mp h8) with h10 h11
    · -- Case x - z = 0 
      exfalso
      have h11 : z = x := by linarith
      rw [show z = x by linarith] at hzx
      all_goals contradiction 
    · 
      linarith
  
  have h12 : z = -x - y := by
    linarith


  have h31 : x ≥ -1 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - 1), sq_nonneg (y - 1)]
  have h32 : x ≤ 1 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x + 1), sq_nonneg (y + 1), sq_nonneg (x - 1), sq_nonneg (y - 1)]
  have h41 : y ≥ -1 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - 1), sq_nonneg (y - 1)]
  have h42 : y ≤ 1 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x + 1), sq_nonneg (y + 1), sq_nonneg (x - 1), sq_nonneg (y - 1)]
  
  have hx2 : x = -1 ∨ x = 0 ∨ x = 1 := by 
    omega 
  have hy2 : y = -1 ∨ y = 0 ∨ y = 1 := by
    omega

  rcases hx2 with h11 | h11 | h11
  · -- Case x = -1 
    rcases hy2 with h22 | h22 | h22
    · -- Case y = -1 
      exfalso 
      rw [show x = -1 by linarith, show y = -1 by linarith] at h2 
      norm_num at h2 
    · -- Case y = 0 
      have hx' : x ^3 - x + k = 0 := by
        linarith
      rw [show x = -1 by linarith] at hx'
      norm_num at hx' 
      linarith
    · -- Case y = 1 
      have hx' : x ^3 - x + k = 0 := by
        linarith
      rw [show x = -1 by linarith] at hx' 
      norm_num at hx' 
      linarith 
  · -- Case x = 0 
    rcases hy2 with h22 | h22 | h22
    · -- Case y = -1 
      have hx' : x ^3 - x + k = 0 := by
        linarith
      rw [show x = 0 by linarith] at hx' 
      norm_num at hx' 
      linarith
    · -- Case y = 0 
      exfalso 
      rw [show x = 0 by linarith, show y = 0 by linarith] at h2
      norm_num at h2 
    · -- Case y = 1 
      have hx' : x ^3 - x + k = 0 := by
        linarith 
      rw [show x = 0 by linarith] at hx' 
      norm_num at hx' 
      linarith
  · -- Case x = 1 
    rcases hy2 with h22 | h22 | h22
    · -- Case y = -1 
      have hx' : x ^3 - x + k = 0 := by
        linarith
      rw [show x = 1 by linarith] at hx' 
      norm_num at hx' 
      linarith
    · -- Case y = 0 
      have hx' : x ^3 - x + k = 0 := by
        linarith 
      rw [show x = 1 by linarith] at hx' 
      norm_num at hx' 
      linarith 
    · -- Case y = 1 
      exfalso 
      rw [show x = 1 by linarith, show y = 1 by linarith] at h2
      norm_num at h2