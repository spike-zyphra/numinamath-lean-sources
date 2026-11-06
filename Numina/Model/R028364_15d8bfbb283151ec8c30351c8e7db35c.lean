import Mathlib

theorem algebra_10604 {a b c : ℝ} (ha : ∀ x, a * (3 * Real.sin x + 2 * Real.cos x + 1) + b * (3 * Real.sin (x - c) + 2 * Real.cos (x - c) + 1) = 1) :
    b * Real.cos c / a = -1 := by
  have eq1 := ha 0
  simp [Real.sin_zero, Real.cos_zero, Real.sin_sub, Real.cos_sub] at eq1 
  have eq2 := ha (Real.pi / 2)
  simp [Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_sub, Real.cos_sub] at eq2 
  have eq3 := ha Real.pi
  simp [Real.sin_pi, Real.cos_pi, Real.sin_sub, Real.cos_sub] at eq3 
  have eq4 := ha (c + Real.pi / 2)
  simp [Real.sin_add, Real.cos_add, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_sub, Real.cos_sub] at eq4 
  have eq5 := ha (c)
  simp [Real.sin_sub, Real.cos_sub] at eq5
  have h1 : Real.sin c = 0 := by
    nlinarith [Real.sin_sq_add_cos_sq c, Real.sin_sq_add_cos_sq c]
  have hcos : Real.cos c = -1 := by
    have h1' : Real.sin c = 0 := h1
    have hcos2 : Real.cos c ^ 2 = 1 := by
      have h : Real.sin c ^ 2 + Real.cos c ^ 2 = 1 := Real.sin_sq_add_cos_sq c
      rw [h1'] at h
      linarith
    have hcos2' : Real.cos c = 1 ∨ Real.cos c = -1 := by
      have hcos2 : Real.cos c ^ 2 = 1 := hcos2
      have : Real.cos c = 1 ∨ Real.cos c = -1 := by
        rw [sq_eq_one_iff] at hcos2
        tauto
      assumption
    cases hcos2' with
    | inl hcos1 =>
      rw [hcos1] at eq1 eq2 eq3 eq4 eq5
      nlinarith [h1, Real.sin_sq_add_cos_sq c]
    | inr hcos1 =>
      linarith
  have hb : b = 1 / 2 := by
    rw [hcos] at eq1 eq2 eq3 eq4 eq5
    nlinarith [h1, Real.sin_sq_add_cos_sq c]
  have ha' : a = 1 / 2 := by
    nlinarith [hb, eq5]
  have hne : a ≠ 0 := by
    linarith [hb, ha']
  rw [hb, hcos, ha']
  norm_num