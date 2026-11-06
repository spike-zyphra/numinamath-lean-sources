import Mathlib

theorem algebra_298058 {a b : ℝ} (ha : 5*a^2+2001*a+9=0) (hb : 9*b^2+2001*b+5=0) (hab : a*b≠1) :
    a/b=9/5 := by

  have ha1 : a ≠ 0 := by 
    by_contra h
    rw [h] at ha
    nlinarith

  have hb1 : b ≠ 0 := by 
    by_contra h
    rw [h] at hb
    nlinarith

  have h1 : 5 * a + 9 / a = -2001 := by 
    have hne : a ≠ 0 := ha1
    have eq1 : 5 * a ^ 2 + 2001 * a + 9 = 0 := by 
      linarith
    field_simp [hne] at *
    nlinarith

  have h2 : 9 * b + 5 / b = -2001 := by 
    have hne : b ≠ 0 := hb1
    have eq1 : 9 * b ^ 2 + 2001 * b + 5 = 0 := by 
      linarith
    field_simp [hne] at *
    nlinarith

  have eq3 : 5 * a ^ 2 * b + 9 * b = 9 * a * b ^ 2 + 5 * a := by
    have eq4 : 5 * a + 9 / a = 9 * b + 5 / b := by
      linarith [h1, h2]
    field_simp [ha1, hb1] at eq4 ⊢
    ring_nf at eq4 ⊢
    nlinarith

  have eq4 : (5 * a - 9 * b) * (a * b - 1) = 0 := by 
    nlinarith [eq3]

  cases' (mul_eq_zero.mp eq4) with h5 h6

  · -- case $5a - 9b = 0$
    have h6 : a / b = 9 / 5 := by 
      have h7 : 5 * a = 9 * b := by linarith
      have h8 : b ≠ 0 := hb1
      field_simp [h8]
      nlinarith
    assumption

  · -- case $a * b - 1 = 0$
    exfalso 
    have h9 : a * b = 1 := by 
      linarith 
    have h9ne : a * b ≠ 1 := by 
      intro h 
      apply hab 
      linarith 
    contradiction