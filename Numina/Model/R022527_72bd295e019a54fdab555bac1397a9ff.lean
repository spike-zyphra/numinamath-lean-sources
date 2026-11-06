import Mathlib

theorem algebra_324103 {a b c : ℂ} (h₀ : a + b ≠ 0) (h₁ : a + c ≠ 0)
    (h₂ : b + c ≠ 0) (h₃ : ∃ x, x^2 + a * x + b = 0 ∧ x^2 + b * x + c = 0 ∧ x = -a)
    (h₄ : ∃ x, x^2 + b * x + c = 0 ∧ x^2 + c * x + a = 0 ∧ x = -b) (h₅ : ∃ x, x^2 + c * x + a = 0 ∧ x^2 + a * x + b = 0 ∧ x = -c) :
    a^2 + b^2 + c^2 = 0 ∧ a^2 * b + b^2 * c + c^2 * a = 0 ∧ a^3 * b^2 + b^3 * c^2 + c^3 * a^2 = 0 ∧
    a = 3 ∧ b = -3 ∧ c = 9 := by
  rcases h₃ with ⟨x, h31, h32, h33⟩
  rcases h₄ with ⟨y, h41, h42, h43⟩
  rcases h₅ with ⟨z, h51, h52, h53⟩
  rw [h33] at h31 h32
  rw [h43] at h41 h42
  rw [h53] at h51 h52
  exfalso
  have eq1 : b = 0 := by
    simp [pow_two] at h31
    all_goals
      tauto
  have eq2 : c = 0 := by
    simp [pow_two] at h41
    all_goals
      tauto
  have eq3 : a = 0 := by
    simp [pow_two] at h51
    all_goals
      tauto
  have h3 : a + b = 0 := by
    rw [eq3, eq1]
    norm_num
  have h7 : a + b ≠ 0 := h₀
  contradiction