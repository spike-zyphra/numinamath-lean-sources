import Mathlib
open Real

theorem algebra_8239 {a b : ℝ} (h₀ : a + b = 0) (h₁ : a ≠ b) :
    (b / a^2) * (a^2 + a + 1) + (a / b^2) * (b^2 + b + 1) = -2 := by
  have ha : a ≠ 0 := by
    intro h
    have hb : b = 0 := by linarith
    rw [h] at h₁
    rw [hb] at h₁
    norm_num at h₁
  have hb : b ≠ 0 := by
    intro h
    have ha' : a = 0 := by linarith
    rw [ha'] at h₁
    rw [h] at h₁
    norm_num at h₁
  have h2 : b = -a := by linarith
  rw [h2]
  have eq1 : ((-a) / a^2) * (a^2 + a + 1) = -a - 1 - 1 / a := by
    have h1 : a ≠ 0 := ha
    field_simp [h1]
    <;> ring
  have eq2 : (a / (-a)^2) * ((-a)^2 + -a + 1) = a - 1 + 1 / a := by
    have h1 : a ≠ 0 := ha
    field_simp [h1]
    <;> ring
  rw [eq1, eq2]
  have h3 : -1 / a + 1 / a = 0 := by
    have h1 : a ≠ 0 := ha
    field_simp [h1]
    <;> ring
  have h4 : -a + a = 0 := by
    linarith
  linarith [h3, h4]