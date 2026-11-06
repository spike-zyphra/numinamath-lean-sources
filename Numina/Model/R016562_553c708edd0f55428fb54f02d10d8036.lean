import Mathlib

theorem algebra_323982 {a b c : ℝ} (h : a * b * c ≠ 0) (h1 : (a + b) / c = (b + c) / a)
    (h2 : (b + c) / a = (c + a) / b) :
    ((a + b) * (b + c) * (c + a)) / (a * b * c) = 8 ∨ ((a + b) * (b + c) * (c + a)) / (a * b * c) = -1 := by

  have ha1 : a ≠ 0 := by
    by_contra h11
    have h111 : a * b * c = 0 := by
      simp [h11]
    contradiction
  have hb1 : b ≠ 0 := by
    by_contra h11
    have h111 : a * b * c = 0 := by
      simp [h11]
    contradiction
  have hc1 : c ≠ 0 := by
    by_contra h11
    have h111 : a * b * c = 0 := by
      simp [h11]
    contradiction
  have eq1 : (a + b) * a = c * (b + c) := by
    have h11 : (a + b) / c = (b + c) / a := h1
    field_simp [hc1, ha1] at h11 ⊢
    <;> nlinarith
  have eq2 : (b + c) * b = a * (c + a) := by
    have h22 : (b + c) / a = (c + a) / b := h2
    field_simp [ha1, hb1] at h22 ⊢
    <;> nlinarith
  by_cases h3 : a + b + c = 0
  · -- Case 1 where a + b + c = 0
    right
    have eq5 : (a + b) * (b + c) * (c + a) = - (a * b * c) := by
      have h4 : c = - (a + b) := by 
        linarith
      have h44 : a + b = -c := by
        linarith
      have h45 : b + c = -a := by 
        nlinarith
      have h46 : c + a = -b := by 
        nlinarith
      rw [show a + b = -c by nlinarith, show b + c = -a by nlinarith, show c + a = -b by nlinarith]
      nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by exact ha1), sq_pos_of_ne_zero (show b ≠ 0 by exact hb1)]
    rw [eq5]
    field_simp [ha1, hb1, hc1]
    <;> nlinarith
  · -- Case 2 where a + b + c ≠ 0
    -- From eq3 and h3
    have eq6 : a - c = 0 := by
      have eq3 : (a - c) * (a + b + c) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 eq3) with h4 h5
      · -- Case a - c = 0
        linarith
      · -- Case a + b + c = 0
        exfalso
        apply h3
        linarith
    -- Similarly:
    have eq7 : b - a = 0 := by
      have eq4 : (b - a) * (a + b + c) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 eq4) with h4 h5
      · -- Case b - a = 0
        linarith
      · -- Case a + b + c = 0
        exfalso
        apply h3
        linarith
    left
    have eq8 : a = c := by
      linarith
    have eq9 : b = a := by
      linarith
    have eq10 : (a + b) * (b + c) * (c + a) = 8 * (a * b * c) := by
      rw [show c = a by linarith [eq8]]
      rw [show b = a by linarith [eq9]]
      nlinarith
    rw [eq10]
    field_simp [ha1, hb1, hc1]
    <;> nlinarith