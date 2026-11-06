import Mathlib

theorem algebra_12619 {a b c : ℝ} (h₀ : a ≠ b) (h₁ : a ≠ c) (h₂ : b ≠ c)
    (h₃ : a ≠ 0) (h₄ : b ≠ 0) (h₅ : c ≠ 0) (h₆ : a + 1 / b = b + 1 / c) (h₇ : b + 1 / c = c + 1 / a) :
    |a * b * c| = 1 := by
  have eq1 : (a - b) * (b * c) = b - c := by
    have h8 : a + 1 / b = b + 1 / c := h₆
    field_simp [h₄, h₅] at h8 ⊢
    linarith
  have eq2 : (b - c) * (a * c) = c - a := by
    have h9 : b + 1 / c = c + 1 / a := h₇
    field_simp [h₅, h₃] at h9 ⊢
    linarith
  have h₈ : a + 1 / b = c + 1 / a := by
    linarith
  have eq3 : (c - a) * (a * b) = a - b := by
    have h9 : a + 1 / b = c + 1 / a := h₈
    field_simp [h₃, h₄] at h9 ⊢
    linarith
  have eq4 : (a - b) * (b - c) * (c - a) * (a * b * c) ^ 2 = (a - b) * (b - c) * (c - a) := by
    have eq4a : (a - b) * (b * c) * ((b - c) * (a * c)) * ((c - a) * (a * b)) = (b - c) * (c - a) * (a - b) := by
      rw [eq1, eq2, eq3]
      all_goals ring
    have eq4b : (a - b) * (b * c) * ((b - c) * (a * c)) * ((c - a) * (a * b)) = (a - b) * (b - c) * (c - a) * (a * b * c) ^ 2 := by
      ring_nf
    rw [eq4b] at eq4a
    linarith
  have h11 : (a - b) * (b - c) * (c - a) ≠ 0 := by
    apply mul_ne_zero
    apply mul_ne_zero
    · -- Show a - b ≠ 0
      intro h14
      apply h₀
      linarith
    · -- Show b - c ≠ 0
      intro h14
      apply h₂
      linarith
    · -- Show c - a ≠ 0
      intro h14
      apply h₁
      linarith
  have eq5 : (a * b * c) ^ 2 = 1 := by
    apply (mul_left_inj' h11).mp
    linarith
  have eq6 : a * b * c = 1 ∨ a * b * c = -1 := by
    have h14 : (a * b * c) ^ 2 = 1 := eq5
    have h15 : a * b * c = 1 ∨ a * b * c = -1 := by
      rw [sq_eq_one_iff] at h14
      tauto
    assumption
  rcases eq6 with (h17 | h17)
  · -- Assume a * b * c = 1
    rw [h17]
    norm_num
  · -- Assume a * b * c = -1
    rw [h17]
    norm_num