import Mathlib

theorem inequalities_156325 (a b c : ℝ) (h₀ : a > b) (h₁ : b > c) :
    4 / (a - c) ≤ 1 / (a - b) + 1 / (b - c) := by 
  have h2 : a - c > 0 := by linarith
  have h3 : a - b > 0 := by linarith
  have h4 : b - c > 0 := by linarith
  have h5 : 0 < (a - b) * (b - c) * (a - c) := by positivity
  have h6 : 1 / (a - b) + 1 / (b - c) - 4 / (a - c) ≥ 0 := by
    have h7 : (1 / (a - b) + 1 / (b - c) - 4 / (a - c)) =
        ((a - c) ^ 2 - 4 * (a - b) * (b - c)) / ((a - b) * (b - c) * (a - c)) := by
      field_simp
      <;> ring_nf
      <;> field_simp
      <;> ring_nf <;> field_simp
      all_goals field_simp
      <;> ring_nf
      all_goals field_simp
      <;> linarith
      all_goals field_simp
      <;> ring_nf <;> field_simp
    rw [h7]
    apply div_nonneg
    nlinarith [sq_nonneg (a - 2 * b), sq_nonneg (c - 2 * b), sq_nonneg (a + c - 2 * b)]
    all_goals positivity
  linarith