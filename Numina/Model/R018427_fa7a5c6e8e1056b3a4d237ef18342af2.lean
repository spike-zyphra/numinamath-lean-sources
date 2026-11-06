import Mathlib

theorem algebra_302839 {a : ℤ} (ha : a^2 - 1 ≠ 0) (h : ∃ x1 x2 : ℤ, x1 ≠ x2 ∧ x1 < 0 ∧ x2 < 0 ∧
    (a^2 - 1) * x1^2 - 2 * (5 * a + 1) * x1 + 24 = 0 ∧ (a^2 - 1) * x2^2 - 2 * (5 * a + 1) * x2 + 24 = 0) :
    a = -2 := by
  rcases h with ⟨x1, x2, hx12, hx1, hx2, heq1, heq2⟩
  have eq1 : (a^2 - 1) * (x1 + x2) = 2 * (5 * a + 1) := by
    have h_sub : (a^2 - 1) * (x1^2 - x2^2) - 2 * (5 * a + 1) * (x1 - x2) = 0 := by 
      nlinarith [heq1, heq2]
    have h_sub' : (a^2 - 1) * (x1 + x2) * (x1 - x2) - 2 * (5 * a + 1) * (x1 - x2) = 0 := by
      ring_nf at h_sub ⊢
      nlinarith
    have h_sub'' : (x1 - x2) * ((a^2 - 1) * (x1 + x2) - 2 * (5 * a + 1)) = 0 := by 
      ring_nf at h_sub' ⊢
      nlinarith
    cases' (mul_eq_zero.mp h_sub'') with h3 h4
    · -- x1 - x2 = 0
      exfalso
      apply hx12
      linarith
    · -- (a^2 -1) * (x1 + x2) -2 * (5 * a + 1) ) = 0
      linarith 
  -- now we can compute the product
  have h1 : (a^2 - 1) * x1 * x2 = 24 := by
    nlinarith [sq_pos_of_ne_zero (show a^2 - 1 ≠ 0 by exact ha), heq1, heq2, eq1, mul_self_nonneg (x1 - x2)]
  have ha2 : a^2 -1 ∣ 24 := by
    use x1 * x2
    all_goals
      nlinarith [h1]
  have h2 : a ≤ 5 := by
    by_contra h2
    push_neg at h2
    have h24 : a^2 -1 > 24 := by
      nlinarith 
    have h24' : a^2 -1 ≤ 24 := by
      apply Int.le_of_dvd (by norm_num) ha2
    nlinarith 
  have h3 : a ≥ -5 := by 
    by_contra h3
    push_neg at h3
    have h24 : a^2 -1 > 24 := by
      nlinarith 
    have h24' : a^2 -1 ≤ 24 := by
      apply Int.le_of_dvd (by norm_num) ha2
    nlinarith 
  interval_cases a <;> norm_num at ha2 h1 eq1 heq1 heq2 <;> try { 
    omega
  }