import Mathlib

theorem algebra_15949 {p q : ℝ} (hpq1 : p ≠ q)(hpq2: p > q)
  (h : (4 * p - 12) / (p ^ 2 + 2 * p - 15) = p + 2)
  (h' : (4 * q - 12) / (q ^ 2 + 2 * q - 15) = q + 2) :
  p - q = 5 := by
  have eq1 : p ^ 2 + 2 * p - 15 ≠ 0 := by
    by_contra h1
    have h2 : (4 * p - 12) / (p ^ 2 + 2 * p - 15) = 0 := by
      rw [h1]
      norm_num
    have h3 : p + 2 = 0 := by linarith [h, h2]
    have h4 : p = -2 := by linarith
    rw [show p = -2 by linarith] at h1
    nlinarith
  have eq2 : q ^ 2 + 2 * q - 15 ≠ 0 := by
    by_contra h1
    have h2 : (4 * q - 12) / (q ^ 2 + 2 * q - 15) = 0 := by
      rw [h1]
      norm_num
    have h3 : q + 2 = 0 := by linarith [h', h2]
    have h4 : q = -2 := by linarith
    rw [show q = -2 by linarith] at h1
    nlinarith
  have eq3 : 4 * p - 12 = (p + 2) * (p ^ 2 + 2 * p - 15) := by
    have h1' : p ^ 2 + 2 * p - 15 ≠ 0 := eq1
    have eq4 : (4 * p - 12) / (p ^ 2 + 2 * p - 15) = p + 2 := h
    field_simp [h1'] at eq4 ⊢
    linarith
  have eq4 : 4 * q - 12 = (q + 2) * (q ^ 2 + 2 * q - 15) := by
    have h2' : q ^ 2 + 2 * q - 15 ≠ 0 := eq2
    have eq5 : (4 * q - 12) / (q ^ 2 + 2 * q - 15) = q + 2 := h'
    field_simp [h2'] at eq5 ⊢
    linarith
  have eq5 : p ^ 3 + 4 * p ^ 2 - 15 * p - 18 = 0 := by
    nlinarith [eq3]
  have eq6 : q ^ 3 + 4 * q ^ 2 - 15 * q - 18 = 0 := by
    nlinarith [eq4]
  have eq7 : (p - 3) * (p + 6) * (p + 1) = 0 := by
    nlinarith [eq5]
  have eq8 : (q - 3) * (q + 6) * (q + 1) = 0 := by
    nlinarith [eq6]
  have hp1 : p = 3 ∨ p = -6 ∨ p = -1 := by
    cases (mul_eq_zero.mp eq7) with
    | inl h8 =>
      cases (mul_eq_zero.mp h8) with
      | inl h9 => 
        left
        linarith
      | inr h10 => 
        right
        left
        linarith
    | inr h11 =>
      right
      right
      linarith
  have hq1 : q = 3 ∨ q = -6 ∨ q = -1 := by
    cases (mul_eq_zero.mp eq8) with
    | inl h8 =>
      cases (mul_eq_zero.mp h8) with
      | inl h9 => 
        left
        linarith
      | inr h10 => 
        right
        left
        linarith
    | inr h11 =>
      right
      right
      linarith
  have hp2 : p ≠ 3 := by
    intro h9
    have h9' : p ^ 2 + 2 * p - 15 = 0 := by
      nlinarith [h9]
    contradiction
  have hq2 : q ≠ 3 := by
    intro h9
    have h9' : q ^ 2 + 2 * q - 15 = 0 := by
      nlinarith [h9]
    contradiction
  rcases hp1 with hp1 | hp1 | hp1 <;> rcases hq1 with hq1 | hq1 | hq1 <;> 
    ( 
      norm_num [hp1, hq1] at *
      <;> try { linarith }
      <;> try { 
        exfalso 
        <;> try { 
          tauto 
        } 
        <;> try { 
          nlinarith 
        } 
      }
    )