import Mathlib

theorem algebra_98872 (x y : ℝ) :
    (2 * y = abs (2 * x + 3) - abs (2 * x - 3)) ∧ (4 * x = abs (y + 2) - abs (y - 2)) ↔
    (-1 ≤ x ∧ x ≤ 1) ∧ (y = 2 * x) := by
  constructor
  · -- Assume the conjunction of the two equations, prove (-1 ≤ x ∧ x ≤ 1) ∧ y = 2 * x
    rintro ⟨h₁, h₂⟩
    by_cases h4 : y ≥ 2
    · -- y ≥ 2
      have h5 : abs (y + 2) = y + 2 := abs_of_nonneg (by linarith)
      have h6 : abs (y - 2) = y - 2 := abs_of_nonneg (by linarith)
      rw [h5, h6] at h₂
      have hx1 : x = 1 := by linarith
      have hy1 : y = 2 := by
        rw [show x = 1 by linarith] at h₁
        cases abs_cases (2 * (1 : ℝ) + 3) with
        | inl h =>
          cases abs_cases (2 * (1 : ℝ) - 3) with
          | inl h2 =>
            linarith
          | inr h2 =>
            linarith
        | inr h =>
          cases abs_cases (2 * (1 : ℝ) - 3) with
          | inl h2 =>
            linarith
          | inr h2 =>
            linarith
      constructor
      · constructor <;> linarith
      · linarith
    · -- y < 2
      by_cases h7 : y ≥ -2
      · -- -2 ≤ y < 2
        have h5 : abs (y + 2) = y + 2 := abs_of_nonneg (by linarith)
        have h6 : abs (y - 2) = 2 - y := by
          have h20 : y - 2 ≤ 0 := by linarith
          rw [abs_of_nonpos h20]
          all_goals nlinarith
        rw [h5, h6] at h₂
        have h8 : y = 2 * x := by linarith
        by_cases h10 : x ≥ 3 / 2
        · -- x ≥ 3/2
          have h11 : abs (2 * x + 3) = 2 * x + 3 := abs_of_nonneg (by nlinarith)
          have h12 : abs (2 * x - 3) = 2 * x - 3 := abs_of_nonneg (by nlinarith)
          rw [h11, h12] at h₁
          nlinarith
        · -- x < 3/2
          by_cases h14 : x ≥ -3 / 2
          · -- -3/2 ≤ x < 3/2
            have h11 : abs (2 * x + 3) = 2 * x + 3 := abs_of_nonneg (by nlinarith)
            have h12 : abs (2 * x - 3) = 3 - 2 * x := by
              rw [abs_of_nonpos (by nlinarith)]
              all_goals nlinarith
            rw [h11, h12] at h₁
            have h9 : y = 2 * x := by linarith
            constructor
            · constructor <;> nlinarith
            · linarith
          · -- x < -3/2
            have h11 : abs (2 * x + 3) = - (2 * x + 3) := abs_of_nonpos (by nlinarith)
            have h12 : abs (2 * x - 3) = 3 - 2 * x := by
              rw [abs_of_nonpos (by nlinarith)]
              all_goals nlinarith
            rw [h11, h12] at h₁
            have hy1 : y = -3 := by linarith
            nlinarith
      · -- y < -2
        have h5 : abs (y + 2) = - (y + 2) := abs_of_nonpos (by linarith)
        have h6 : abs (y - 2) = - (y - 2) := abs_of_nonpos (by linarith)
        rw [h5, h6] at h₂
        have hx1 : x = -1 := by linarith
        rw [show x = -1 by linarith] at h₁
        norm_num [abs_of_nonneg, abs_of_neg] at h₁
        all_goals nlinarith
  · -- Assume (-1 ≤ x ∧ x ≤ 1) ∧ y = 2 * x, prove both equations
    rintro ⟨⟨h₁, h₂⟩, h₃⟩
    constructor
    · -- First equation
      have h4 : -1 ≤ x := h₁
      have h5 : x ≤ 1 := h₂
      have h6 : 2 * x + 3 ≥ 0 := by nlinarith
      have h7 : 2 * x - 3 ≤ 0 := by nlinarith
      have h8 : abs (2 * x + 3) = 2 * x + 3 := abs_of_nonneg h6
      have h9 : abs (2 * x - 3) = 3 - 2 * x := by
        rw [abs_of_nonpos h7]
        all_goals nlinarith
      rw [h8, h9]
      nlinarith [h₃]
    · -- Second equation
      have h4 : -1 ≤ x := h₁
      have h5 : x ≤ 1 := h₂
      have h10 : y ≥ -2 := by nlinarith [h₃]
      have h11 : y ≤ 2 := by nlinarith [h₃]
      have h12 : abs (y + 2) = y + 2 := abs_of_nonneg (by nlinarith)
      have h13 : abs (y - 2) = 2 - y := by
        have h14 : y - 2 ≤ 0 := by nlinarith
        rw [abs_of_nonpos h14]
        all_goals nlinarith
      rw [h12, h13]
      nlinarith [h₃]