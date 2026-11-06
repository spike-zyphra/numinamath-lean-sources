import Mathlib

theorem algebra_277365 (v : ℝ) (h : v > 0) (h1 : 1 / v = 1 / (v - 36 / 60) + 1 / 60) :
    1 / v = 40 / 60 := by
  have h2 : v - 36 / 60 ≠ 0 := by
    by_contra h3
    have h4 : 1 / v = 1 / (v - 36 / 60) + 1 / 60 := h1
    rw [show v - 36 / 60 = 0 by linarith] at h4
    field_simp at h4
    all_goals nlinarith
  have h3 : v * 60 - 36 ≠ 0 := by
    intro h4
    have h5 : v - 36 / 60 = 0 := by
      linarith
    contradiction

  field_simp [h2, h3] at h1 ⊢
  <;> ring_nf at h1 ⊢
  <;> nlinarith [sq_pos_of_pos h, sq_nonneg (v * 60 - 36), sq_nonneg (v * 60), sq_nonneg (v - 3 / 5), sq_nonneg (v - 3 / 2)]
  <;> try { linarith }
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { norm_num }
  <;> try { linarith }
  <;> try { tauto }
  <;> try { nlinarith [sq_nonneg (v * 60 - 36) , sq_nonneg (v - 3 / 5), sq_nonneg (v * 2 - 3)] }