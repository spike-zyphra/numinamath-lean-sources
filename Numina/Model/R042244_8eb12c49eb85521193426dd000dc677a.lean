import Mathlib

theorem algebra_178351 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 = c^2) (h' : ∃ d, b = a + d ∧ c = b + d) :
    a / b = 3 / 4 := by
  rcases h' with ⟨d, h1, h2⟩
  have eq1 : c = 2 * b - a := by
    have eq2 : d = b - a := by
      linarith
    rw [h2, eq2]
    all_goals
      nlinarith [h1]
  have eq2 : a ^ 2 + b ^ 2 = (2 * b - a) ^ 2 := by
    rw [eq1] at h
    linarith
  have eq5 : 3 * b ^ 2 = 4 * a * b := by
    nlinarith [eq2]
  have eq6 : a = 3 / 4 * b := by
    have hneq : b ≠ 0 := by linarith
    apply (mul_left_inj' hneq).mp
    linarith [eq5]
  have eq7 : a / b = 3 / 4 := by
    have hneq : b ≠ 0 := by linarith
    field_simp [hneq]
    <;> linarith [eq6]
  exact_mod_cast eq7