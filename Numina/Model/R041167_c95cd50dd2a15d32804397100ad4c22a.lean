import Mathlib

theorem algebra_284901 (p q r : ℝ) (hpqr : p ≠ q ∧ p ≠ r ∧ q ≠ r)
    (h : p^3-9*p^2+8*p+2=0 ∧ q^3-9*q^2+8*q+2=0 ∧ r^3-9*r^2+8*r+2=0) :
    1/p^2+1/q^2+1/r^2=25 := by 
  rcases h with ⟨hp, hq, hr⟩
  rcases hpqr with ⟨hpq, hpr, hqr⟩
  have eq1 : p ≠ 0 := by
    by_contra h1
    rw [h1] at hp
    nlinarith
  have eq2 : q ≠ 0 := by
    by_contra h1
    rw [h1] at hq
    nlinarith
  have eq3 : r ≠ 0 := by
    by_contra h1
    rw [h1] at hr
    nlinarith 
  -- Subtract the equations
  -- Equation for q, subtract by p
  have eq3 : q^2 + p*q + p^2 - 9*(p + q) + 8 = 0 := by 
    have eq5 : p - q ≠ 0 := by
      intro h
      apply hpq
      linarith
    have h7 : (q ^ 3 - 9 * q ^ 2 + 8 * q + 2) - (p ^ 3 - 9 * p ^ 2 + 8 * p + 2) = 0 := by
      linarith [hp, hq]
    have eq8 : (q - p) * (q^2 + p*q + p^2 - 9*(p + q) + 8) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp eq8) with h9 h10
    · -- Since q - p ≠ 0, because hpq: p ≠ q
      exfalso
      apply eq5
      linarith
    · 
      linarith
  -- Equation for r, subtract by p  
  have eq4 : r^2 + p*r + p^2 - 9*(p + r) + 8 = 0 := by 
    have eq5 : p - r ≠ 0 := by
      intro h
      apply hpr
      linarith
    have h7 : (r ^ 3 - 9 * r ^ 2 + 8 * r + 2) - (p ^ 3 - 9 * p ^ 2 + 8 * p + 2) = 0 := by
      linarith [hp, hr]
    have eq8 : (r - p) * (r^2 + p*r + p^2 - 9*(p + r) + 8) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp eq8) with h9 h10
    · -- Since r - p ≠ 0, because hpr: p ≠ r
      exfalso
      apply eq5
      linarith
    · 
      linarith
  -- Equation for r, subtract by q
  have eq5 : r^2 + q*r + q^2 - 9*(q + r) + 8 = 0 := by 
    have eq5 : q - r ≠ 0 := by
      intro h
      apply hqr
      linarith
    have h7 : (r ^ 3 - 9 * r ^ 2 + 8 * r + 2) - (q ^ 3 - 9 * q ^ 2 + 8 * q + 2) = 0 := by
      linarith [hq, hr]
    have eq8 : (r - q) * (r^2 + q*r + q^2 - 9*(q + r) + 8) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp eq8) with h9 h10
    · -- Since r - q ≠ 0, because hqr: q ≠ r
      exfalso
      apply eq5
      linarith
    · 
      linarith
  -- Prove p + q + r = 9
  have eq6 : p + q + r = 9 := by 
    have e1 : (q - r) * (p + q + r - 9) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.mp e1) with h13 h14
    · 
      exfalso
      apply hqr
      linarith 
    · 
      linarith
  -- Prove p * q + p * r + q * r = 8
  have eq7 : p * q + p * r + q * r = 8 := by 
    nlinarith 
  -- Prove p * q * r = -2
  have eq8 : p * q * r = -2 := by 
    nlinarith
  have eq14 : 1/p^2 + 1/q^2 + 1/r^2 = (q^2 * r^2 + p^2 * r^2 + p^2 * q^2) / (p^2 * q^2 * r^2) := by
    field_simp [eq1, eq2, eq3]
    <;> ring
  have eq4 : q^2 * r^2 + p^2 * r^2 + p^2 * q^2 = 100 := by
    nlinarith 
  have eq5 : p^2 * q^2 * r^2 = 4 := by
    nlinarith 
  rw [eq14]
  rw [eq4, eq5]
  all_goals norm_num