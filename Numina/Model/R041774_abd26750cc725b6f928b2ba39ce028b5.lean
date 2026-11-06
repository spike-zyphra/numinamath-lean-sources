import Mathlib

theorem algebra_192590 {x y : ℝ} : 
    x^2 + x * y + y = 1 ∧ y^2 + x * y + x = 5 ↔ 
    (x = -1 ∧ y = -2) ∨ (x = -1 ∧ y = 3):= by 
  constructor
  · -- Assume the equations hold, prove the conclusion
    rintro ⟨h₁, h₂⟩
    have h3 : (y - x) * (y + x - 1) = 4 := by
      nlinarith
    have h4 : (x + y) ^ 2 + x + y = 6 := by
      nlinarith
    have h5 : (x + y - 2) * (x + y + 3) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h5) with h6 h7
    · -- Case h6 : x + y - 2 = 0
      have h7 : x + y = 2 := by linarith
      have h8 : x = -1 := by
        have eq1 : x + y = 2 := by linarith
        have eq2 : y = 2 - x := by linarith
        rw [eq2] at h₁
        nlinarith
      have h9 : y = 3 := by
        linarith
      right
      exact ⟨h8, h9⟩
    · -- Case h7 : x + y + 3 = 0
      have h7a : x + y = -3 := by linarith
      have h8 : x = -1 := by
        have eq1 : x + y = -3 := by linarith
        have eq2 : y = -3 - x := by linarith
        rw [eq2] at h₁
        nlinarith
      have h9 : y = -2 := by
        linarith
      left
      exact ⟨h8, h9⟩
  · -- Assume the conclusion holds, prove the equations
    rintro (h | h)
    · -- (x = -1 ∧ y = -2)
      rcases h with ⟨rfl, rfl⟩
      constructor
      · -- First equation
        norm_num
      · -- Second equation
        norm_num
    · -- (x = -1 ∧ y = 3)
      rcases h with ⟨rfl, rfl⟩
      constructor
      · -- First equation
        norm_num
      · -- Second equation
        norm_num