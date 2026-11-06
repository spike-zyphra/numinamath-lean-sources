import Mathlib

theorem algebra_262604 (v1 v2 : ℝ) (h1 : v1 > 0) (h2 : v2 > 0)
    (h3 : 120 / v1 = 120 / v2 - 18 / 60) (h4 : 120 / (v1 - 12) = 120 / (v2 * 1.1)) :
    v1 = 100 ∧ v2 = 80 := by
  have eq3 : 120 * v2 - 120 * v1 + 0.3 * (v1 * v2) = 0 := by
    have h5 : v1 ≠ 0 := by linarith
    have h6 : v2 ≠ 0 := by linarith
    field_simp [h5, h6] at h3 ⊢
    ring_nf at h3 ⊢
    nlinarith [sq_pos_of_pos h1, sq_pos_of_pos h2]
  -- Convert the second equation
  have eq4 : 132 * v2 = 120 * (v1 - 12) := by
    have h7 : v1 - 12 ≠ 0 := by
      by_contra h
      have : v1 = 12 := by linarith
      rw [this] at h4
      field_simp [show v2 ≠ 0 by linarith] at h4
      <;> nlinarith
    have h8 : v2 * (1.1 : ℝ) ≠ 0 := by
      have h9 : v2 ≠ 0 := by linarith
      have h10 : (1.1 : ℝ) ≠ 0 := by norm_num
      field_simp [h9, h10]
    field_simp [h7, h8] at h4 ⊢
    ring_nf at h4 ⊢
    nlinarith
  have eq5 : 132 * v2 = 120 * (v1 - 12) := eq4
  have eq6 : 120 * (v2 - v1) + 0.3 * (v1 * v2) = 0 := by
    linarith [eq3]
  have v1_eq : v1 = (11 * v2 + 120) / 10 := by
    linarith [eq5]
  rw [v1_eq] at eq6
  ring_nf at eq6 ⊢
  have h10 : (v2 - 80) * (v2 + 100 / 11) = 0 := by
    nlinarith
  cases (mul_eq_zero.1 h10) with
  | inl h12 => 
    have h13 : v2 = 80 := by linarith
    have h14 : v1 = 100 := by
      rw [h13] at v1_eq
      linarith
    exact ⟨h14, h13⟩
  | inr h13 => 
    have h14 : v2 < 0 := by nlinarith
    linarith