import Mathlib

open Real
open scoped BigOperators

theorem other_71083 :
  {(a, b) : ℤ × ℤ | a^2 + b^2 = a + b}.ncard = 4 := by

  have h1 : {(a, b) : ℤ × ℤ | a^2 + b^2 = a + b} = {(0,0), (1,0), (0,1), (1,1)} := by
    ext ⟨a,b⟩
    simp
    constructor
    · -- Assume a^2 + b^2 = a + b
      intro h
      have h2 : a^2 - a ≥ 0 := by nlinarith [sq_nonneg (a - 1), sq_nonneg (a)]
      have h3 : b^2 - b ≥ 0 := by nlinarith [sq_nonneg (b - 1), sq_nonneg (b)]

      have h4 : a^2 - a + (b^2 - b) = 0 := by linarith

      have h5 : a^2 - a = 0 := by linarith [h4, h2, h3]
      have h6 : b^2 - b = 0 := by linarith [h4, h2, h3]

      have ha : a = 0 ∨ a = 1 := by
        have : a * (a - 1) = 0 := by linarith
        cases (mul_eq_zero.mp this) with
        | inl h_left => 
            left
            linarith
        | inr h_right => 
            right
            linarith

      have hb : b = 0 ∨ b = 1 := by
        have : b * (b - 1) = 0 := by linarith
        cases (mul_eq_zero.mp this) with
        | inl h_left => 
            left
            linarith
        | inr h_right => 
            right
            linarith

      rcases ha with ha | ha <;> rcases hb with hb | hb <;> 
        (rw [ha, hb]; tauto)

    · -- Show that if (a, b) ∈ {(0,0), (1,0), (0,1), (1,1)}, then a^2 + b^2 = a + b
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      all_goals
        norm_num

  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> rfl