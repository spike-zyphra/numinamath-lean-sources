import Mathlib

theorem algebra_163235 (x y : ℝ) :
    y^4 - y^2 = 0 ∧ x * y^3 - x * y = 0 ∧ x^3 * y - x * y = 0 ∧ x^4 - x^2 = 0 ↔
    (x = 0 ∧ y = 0) ∨ (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = -1) ∨ (x = 1 ∧ y = 0) ∨
    (x = -1 ∧ y = 0) ∨ (x = 1 ∧ y = 1) ∨ (x = -1 ∧ y = -1) ∨ (x = 1 ∧ y = -1) ∨
    (x = -1 ∧ y = 1) := by
  constructor
  · -- Forward direction: If $(x, y)$ satisfies all four equations, then it is one of the 9 pairs.
    rintro ⟨h1, h2, h3, h4⟩
    
    have hy : y^2 * (y^2 - 1) = 0 := by
      nlinarith
    
    have hy2 : y^2 = 0 ∨ y^2 - 1 = 0 := by
      cases (mul_eq_zero.mp hy) with
      | inl h => 
        left
        linarith
      | inr h => 
        right
        linarith

    have hy_cases : y = 0 ∨ y = 1 ∨ y = -1 := by
      cases hy2 with
      | inl h => 
        have : y = 0 := by nlinarith
        simp [this]
      | inr h => 
        have h2 : y^2 = 1 := by linarith
        have : y = 1 ∨ y = -1 := by
          rw [sq_eq_one_iff] at h2
          tauto
        tauto

    have hx2 : x^2 * (x^2 - 1) = 0 := by
      nlinarith
    
    have hx2_cases : x^2 = 0 ∨ x^2 - 1 = 0 := by
      cases (mul_eq_zero.mp hx2) with
      | inl h => 
        left
        linarith
      | inr h => 
        right
        linarith

    have hx_cases : x = 0 ∨ x = 1 ∨ x = -1 := by
      cases hx2_cases with
      | inl h => 
        have : x = 0 := by nlinarith
        simp [this]
      | inr h => 
        have hx2_1 : x^2 = 1 := by linarith
        have : x = 1 ∨ x = -1 := by
          rw [sq_eq_one_iff] at hx2_1
          tauto
        tauto

    rcases hx_cases with hx | hx | hx <;> rcases hy_cases with hy | hy | hy <;> 
      simp [hx, hy]

  · -- Backward direction: If $(x, y)$ is one of the 9 pairs, then it satisfies all 4 equations.
    rintro (h | h | h | h | h | h | h | h | h)
    · -- Case (0, 0)
      rcases h with ⟨rfl, rfl⟩
      constructor
      · -- First equation
        norm_num
      constructor
      · -- Second equation
        norm_num
      constructor
      · -- Third equation
        norm_num
      · -- Fourth equation
        norm_num
    · -- Case (0, 1)
      rcases h with ⟨rfl, rfl⟩
      constructor
      · -- First equation
        norm_num
      constructor
      · -- Second equation
        norm_num
      constructor
      · -- Third equation
        norm_num
      · -- Fourth equation
        norm_num
    · -- Case (0, -1)
      rcases h with ⟨rfl, rfl⟩
      constructor
      · -- First equation
        norm_num
      constructor
      · -- Second equation
        norm_num
      constructor
      · -- Third equation
        norm_num
      · -- Fourth equation
        norm_num
    · -- Case (1, 0)
      rcases h with ⟨rfl, rfl⟩
      constructor
      · -- First equation
        norm_num
      constructor
      · -- Second equation
        norm_num
      constructor
      · -- Third equation
        norm_num
      · -- Fourth equation
        norm_num
    · -- Case (-1, 0)
      rcases h with ⟨rfl, rfl⟩
      constructor
      · -- First equation
        norm_num
      constructor
      · -- Second equation
        norm_num
      constructor
      · -- Third equation
        norm_num
      · -- Fourth equation
        norm_num
    · -- Case (1, 1)
      rcases h with ⟨rfl, rfl⟩
      constructor
      · -- First equation
        norm_num
      constructor
      · -- Second equation
        norm_num
      constructor
      · -- Third equation
        norm_num
      · -- Fourth equation
        norm_num
    · -- Case (-1, -1)
      rcases h with ⟨rfl, rfl⟩
      constructor
      · -- First equation
        norm_num
      constructor
      · -- Second equation
        norm_num
      constructor
      · -- Third equation
        norm_num
      · -- Fourth equation
        norm_num
    · -- Case (1, -1)
      rcases h with ⟨rfl, rfl⟩
      constructor
      · -- First equation
        norm_num
      constructor
      · -- Second equation
        norm_num
      constructor
      · -- Third equation
        norm_num
      · -- Fourth equation
        norm_num
    · -- Case (-1, 1)
      rcases h with ⟨rfl, rfl⟩
      constructor
      · -- First equation
        norm_num
      constructor
      · -- Second equation
        norm_num
      constructor
      · -- Third equation
        norm_num
      · -- Fourth equation
        norm_num