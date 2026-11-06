import Mathlib

theorem algebra_2823 {a b c : ℝ} (habc : a * b * c ≠ 0) (h₀ : a / b = b / c) (h₁ : b / c = c / a) :
    (3 * a + 2 * b + c) / (a - 2 * b - 3 * c) = - 3 / 2 := by
  have hb : b ≠ 0 := by
    by_contra h
    have : a * b * c = 0 := by
      rw [h]
      norm_num
    contradiction
  have ha : a ≠ 0 := by
    by_contra h
    have : a * b * c = 0 := by
      rw [h]
      norm_num
    contradiction
  have hc : c ≠ 0 := by
    by_contra h
    have : a * b * c = 0 := by
      rw [h]
      norm_num
    contradiction
  have h2 : a * c = b ^ 2 := by 
    have h2 : b ≠ 0 := hb
    have h3 : c ≠ 0 := hc
    field_simp [hb, hc] at h₀ ⊢
    nlinarith
  have h3 : b * a = c ^ 2 := by
    have hb' : b ≠ 0 := hb
    have ha' : a ≠ 0 := ha
    field_simp [hb, hc, ha] at h₁ ⊢
    nlinarith
  have h4 : b ^ 3 = c ^ 3 := by 
    have eq1 : a * c = b ^ 2 := h2
    have eq2 : b * a = c ^ 2 := h3
    have eq3 : b ^ 3 = c ^ 3 := by
      have eq4 : c ^ 2 = b * a := by
        linarith
      have eq5 : c ^ 3 = b * a * c := by
        calc
          c ^ 3 = c * c ^ 2 := by ring
          _ = c * (b * a) := by rw [eq4]
          _ = (b * a) * c := by ring
      have eq6 : b ^ 3 = b * (a * c) := by 
        calc
          b ^ 3 = b * (b ^ 2) := by ring
          _ = b * (a * c) := by rw [eq1]
      rw [eq6, eq5]
      all_goals linarith
    exact_mod_cast eq3
  have h5 : b = c := by 
    have h6 : b ^ 3 = c ^ 3 := h4
    have h7 : b = c := by 
      have h8 : b ^ 3 - c ^ 3 = 0 := by 
        linarith
      have h9 : (b - c) * (b ^ 2 + b * c + c ^ 2) = 0 := by 
        ring_nf at h8 ⊢ 
        linarith 
      cases' (mul_eq_zero.1 h9) with h10 h11 
      · -- `b - c = 0` 
        linarith 
      · -- `b ^ 2 + b * c + c ^ 2 = 0` 
        have h12 : b ^ 2 + b * c + c ^ 2 > 0 := by 
          nlinarith [sq_pos_of_ne_zero (show b ≠ 0 by assumption), sq_pos_of_ne_zero (show c ≠ 0 by assumption), sq_nonneg (b - c), sq_nonneg (b + c)]
        linarith 
    exact h7 
  have h6 : a = b := by 
    have h2' : a * c = b ^ 2 := h2
    rw [show c = b by linarith [h5]] at h2'
    have h7 : a * b = b ^ 2 := h2'
    have h8 : a = b := by 
      apply (mul_left_inj' hb).mp 
      linarith 
    linarith 
  have h7 : a = c := by 
    linarith [h6, h5] 
  -- Now we have a = b = c, so we can compute the expression 
  have h8 : 3 * a + 2 * b + c = 6 * a := by 
    have h5' : b = a := by linarith [h6]
    have h7' : c = a := by linarith [h7]
    rw [show b = a by linarith [h5'], show c = a by linarith [h7']]
    linarith 
  have h9 : a - 2 * b - 3 * c = -4 * a := by 
    have h5' : b = a := by linarith [h6]
    have h7' : c = a := by linarith [h7]
    rw [show b = a by linarith [h5'], show c = a by linarith [h7']]
    linarith 
  have h10 : a - 2 * b - 3 * c ≠ 0 := by 
    by_contra h
    have h14 : a - 2 * b - 3 * c = 0 := by linarith 
    have h15 : -4 * a = 0 := by 
      linarith [h9, h14] 
    have h16 : a = 0 := by 
      linarith 
    contradiction 
  rw [h8, h9] 
  have h13 : a ≠ 0 := ha 
  field_simp [h13] 
  <;> nlinarith