import Mathlib

theorem algebra_220255 {p q : ℤ} (hp : p ≠ 0) (hq : q ≠ 0)
    (h : ∃ x y, x ≠ y ∧ x^2 + p * x + q = 0 ∧ y^2 + p * y + q = 0 ∧
      p = x ∧ q = y) :
    p = 1 ∧ q = -2 := by
  rcases h with ⟨x, y, hneq, hx, hy, hp_eq, hq_eq⟩
  have eq1 : 2 * x^2 + y = 0 := by
    rw [show p = x by linarith [hp_eq], show q = y by linarith [hq_eq]] at hx
    nlinarith
  have eq2 : y * (y + x + 1) = 0 := by
    rw [show p = x by linarith [hp_eq], show q = y by linarith [hq_eq]] at hy
    nlinarith
  have hyne0 : y ≠ 0 := by 
    intro h0
    have hq0 : q = 0 := by
      linarith [hq_eq, h0]
    contradiction
  have eq3 : y + x + 1 = 0 := by
    apply (mul_left_inj' hyne0).mp 
    linarith
  have eq4 : y = -x - 1 := by 
    omega
  rw [eq4] at eq1 
  have eq5 : 2 * x^2 - x - 1 = 0 := by
    nlinarith
  have eq6 : x = 1 := by 
    have h1 : 2 * x^2 - x - 1 = 0 := eq5
    have : 2 * x^2 = x + 1 := by linarith 
    have h3 : x * (2 * x - 1) = 1 := by 
      nlinarith 
    have h4 : x = 1 ∨ x = -1 := by 
      apply Int.eq_one_or_neg_one_of_mul_eq_one 
      exact h3
    rcases h4 with (h5 | h5)
    · linarith 
    · -- x = -1, then y = 0 which is a contradiction.
      have h7 : x = -1 := h5
      have h8 : y = 0 := by 
        linarith [eq4, h7] 
      contradiction 
  have eq7 : y = -2 := by 
    rw [eq6] at eq4 
    omega 
  have hp1 : p = 1 := by 
    linarith [hp_eq, eq6] 
  have hq2 : q = -2 := by 
    linarith [hq_eq, eq7] 
  exact ⟨hp1, hq2⟩