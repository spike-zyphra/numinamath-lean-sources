import Mathlib

theorem algebra_2430 {a : ℝ} (ha : a ≠ 0) (ha1 : ∃ q : ℚ, a = q) :
    ¬(∃ z : ℤ, z = 1 / a - 2 / a + 3 / a - 4 / a + 5 / a ∧ z = 0) := by
  rintro ⟨z, h_eq, h_zero⟩
  have h1 : (z : ℝ) = 0 := by exact_mod_cast h_zero
  have eq1 : (z : ℝ) = 1 / a - 2 / a + 3 / a - 4 / a + 5 / a := by
    rw [h_eq]
    all_goals norm_num
  rw [eq1] at h1
  have eq2 : (1 / a - 2 / a + 3 / a - 4 / a + 5 / a : ℝ) = (3 / a : ℝ) := by
    field_simp [ha]
    <;> ring
  rw [eq2] at h1
  have eq3 : (3 / a : ℝ) = 0 := by
    linarith [h1]
  have eq4 : (3 : ℝ) = 0 := by
    field_simp [ha] at eq3
    <;> linarith
  norm_num at eq4