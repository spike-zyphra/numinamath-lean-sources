import Mathlib

theorem algebra_296969 (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) (h : 1 / a = 1 / b + 1 / c) :
    a = b * c / (b + c) := by
  have h1 : a ≠ 0 := by
    by_contra h1
    rw [h1] at h
    field_simp [show b ≠ 0 by linarith, show c ≠ 0 by linarith] at h
    all_goals linarith 
  have h2 : b * c ≠ 0 := by
    apply mul_ne_zero
    linarith
    linarith
  have eq1 : 1 / b + 1 / c = (b + c) / (b * c) := by
    field_simp [show b ≠ 0 by linarith, show c ≠ 0 by linarith]
    <;> ring
  rw [eq1] at h
  have h3 : a * (b + c) = b * c := by
    have h4 : a ≠ 0 := h1
    have h5 : b + c ≠ 0 := by
      have hb1 : 0 < b := hb
      have hc1 : 0 < c := hc
      linarith
    field_simp [h4, show b ≠ 0 by linarith, show c ≠ 0 by linarith, show b * c ≠ 0 by
      apply mul_ne_zero (by linarith) (by linarith)
    ] at h ⊢
    <;> nlinarith [mul_pos hb hc]
  have h4 : a = b * c / (b + c) := by
    have h5 : b + c ≠ 0 := by
      have hb1 : 0 < b := hb
      have hc1 : 0 < c := hc
      linarith
    field_simp [h5]
    <;> nlinarith [mul_pos hb hc]
  exact h4