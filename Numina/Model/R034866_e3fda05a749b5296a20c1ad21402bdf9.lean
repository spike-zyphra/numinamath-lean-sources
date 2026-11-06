import Mathlib

theorem algebra_3607 {t : ℝ} (ht : t ≠ 0) (h1 : t + 1 / t ^ 2 = 351 / 28) (h2 : 2 * t + 3 / t ^ 2 = 1045 / 28) :
    7 * t = 2 := by
  have h3 : (351 / 28) - t = 1 / t ^ 2 := by
    have eq1 : t + 1 / t ^ 2 = 351 / 28 := h1
    have eq2 : (351 / 28) - t = 1 / t ^ 2 := by
      have eq3 : (351 / 28) - t = 1 / t ^ 2 := by
        field_simp [ht] at eq1 ⊢
        <;> nlinarith
      linarith
    exact eq2
  have h4' : 3 / t^2 = 3 * (1 / t^2) := by
    field_simp [ht]
    <;> ring_nf <;> field_simp [ht]
  have eq1 : 3 / t ^ 2 = 3 * ((351 / 28) - t) := by
    calc
      3 / t ^ 2 = 3 * (1 / t ^ 2) := by rw [h4']
      _ = 3 * ((351 / 28) - t) := by rw [h3]
  have h4 : 2 * t + 3 / t ^ 2 = 1045 / 28 := h2
  rw [show 3 / t ^ 2 = 3 * ((351 / 28) - t) by linarith [eq1]] at h4
  have ht' : t = 2 / 7 := by
    field_simp [ht] at h4
    nlinarith
  linarith [ht']