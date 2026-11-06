import Mathlib

theorem algebra_207871 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hdist : a ≠ b ∧ a ≠ c ∧ b ≠ c) (h1 : a * (c / a)^2 + b * (c / a) + c = 0) :
    ∃ x, b * x^2 + c * x + a = 0 ∧ c * x^2 + a * x + b = 0 ∧
    x * (c / a) * (b / c) * (a / b) = 1 := by
  have h2 : c * (a + b + c) = 0 := by
    have eq1 : a * (c / a) ^ 2 + b * (c / a) + c = 0 := h1
    have eq4 : a * (c / a) ^ 2 + b * (c / a) + c = (c ^ 2 + b * c + a * c) / a := by
      field_simp
      <;> ring
    rw [eq4] at eq1
    have eq5 : c ^ 2 + b * c + a * c = 0 := by
      field_simp at eq1
      all_goals linarith
    have eq6 : c * (a + b + c) = 0 := by
      linarith
      all_goals nlinarith
    linarith
  have h3 : a + b + c = 0 := by
    apply_fun (fun x => x / c) at h2
    field_simp [hc] at h2
    linarith
    all_goals nlinarith
  use 1
  constructor
  · -- Show that 1 is a solution to the second equation
    have eq1 : b * (1 : ℝ) ^ 2 + c * (1 : ℝ) + a = 0 := by
      nlinarith
    simpa using eq1
  constructor
  · -- Show that 1 is a solution to the third equation
    have eq2 : c * (1 : ℝ) ^ 2 + a * (1 : ℝ) + b = 0 := by
      nlinarith
    simpa using eq2
  · -- Show that the product is 1
    field_simp [ha, hb, hc]
    <;> ring