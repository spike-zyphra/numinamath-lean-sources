import Mathlib

theorem algebra_12234 :
    {(a, b) : ℝ × ℝ | ∃ d, a = 10 + d ∧ b = a + d ∧ a * b = b + d}.ncard = 2 := by 
  have : {(a, b) : ℝ × ℝ | ∃ d, a = 10 + d ∧ b = a + d ∧ a * b = b + d} = {(4, -2), (5 / 2, -5)} := by
    ext ⟨a, b⟩
    simp
    constructor
    · rintro ⟨d, ha, hb, hab⟩
      have eq1 : b = 2 * a - 10 := by linarith
      rw [ha] at hb
      have d_eq : d = a - 10 := by linarith
      rw [eq1, d_eq] at hab
      have quad_eq : 2 * a ^ 2 - 13 * a + 20 = 0 := by linarith
      have : (a = 4 ∨ a = 5 / 2) := by 
        have h1 : 2 * a ^ 2 - 13 * a + 20 = 0 := quad_eq
        have : (2 * a - 5) * (a - 4) = 0 := by linarith
        cases (mul_eq_zero.mp this) with
        | inl h2 => 
          right
          linarith
        | inr h3 =>
          left
          linarith
      cases this with
      | inl ha4 =>
        left
        constructor
        · exact ha4
        · rw [ha4] at eq1
          linarith
      | inr ha52 =>
        right
        constructor
        · exact ha52
        · rw [ha52] at eq1
          linarith
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · use -6
        constructor
        · norm_num
        · constructor
          · norm_num
          · norm_num
      · use -15 / 2
        constructor
        · norm_num
        · constructor
          · norm_num
          · norm_num
  rw [this]
  norm_num