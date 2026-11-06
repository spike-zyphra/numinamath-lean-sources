import Mathlib

theorem algebra_3494 {x y : ℝ} (hy : y ≠ -1 ∧ y ≠ 0) (h1 : 4 * (6 / y - 6 / (y + 1)) - 3 * (x - 4) = 8) (h2 : 3 * (x - 3) - 4 * (12 / (y + 1) - 12 / y) = 7) :
    x = 2 + 2 / 3 := by
  rcases hy with ⟨hy1, hy2⟩
  have eq1 : 4 * (6 / y - 6 / (y + 1)) = 24 / (y * (y + 1)) := by
    field_simp [(show y + 1 ≠ 0 by intro h; apply hy1; linarith), (show y ≠ 0 by exact hy2)]
    <;> ring_nf
    <;> field_simp [(show y + 1 ≠ 0 by intro h; apply hy1; linarith), (show y ≠ 0 by exact hy2)]
    <;> ring
  have eq5 : 4 * (12 / (y + 1) - 12 / y) = -48 / (y * (y + 1)) := by
    field_simp [(show y + 1 ≠ 0 by intro h; apply hy1; linarith), (show y ≠ 0 by exact hy2)]
    <;> ring_nf
    <;> field_simp [(show y + 1 ≠ 0 by intro h; apply hy1; linarith), (show y ≠ 0 by exact hy2)]
    <;> ring
  rw [eq1] at h1
  have eq33c1 : 24 / (y * (y + 1)) = 3 * x - 4 := by
    have h3 : 24 / (y * (y + 1)) - 3 * (x - 4) = 8 := by
      linarith
    have eq38c1 : 24 / (y * (y + 1)) = 3 * x - 4 := by
      field_simp [(show y + 1 ≠ 0 by intro h; apply hy1; linarith), (show y ≠ 0 by exact hy2)] at h3 ⊢
      nlinarith
      <;> nlinarith
      all_goals linarith
    tauto
  rw [eq5] at h2
  norm_num at h1 h2 ⊢
  field_simp [(show y + 1 ≠ 0 by intro h; apply hy1; linarith), (show y ≠ 0 by exact hy2)] at h1 h2 ⊢
  <;> nlinarith [sq_pos_of_pos (show (0 : ℝ) < 3 by norm_num)]