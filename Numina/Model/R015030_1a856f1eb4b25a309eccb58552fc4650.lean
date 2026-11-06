import Mathlib

theorem algebra_197134 (x : ℝ) :
    Real.sqrt ((2 - 3 * abs x) ^ 2) = 2 + 3 * x ↔ -2 / 3 ≤ x ∧ x ≤ 0 := by
  constructor
  · -- Assume Real.sqrt ((2 - 3 * abs x) ^ 2) = 2 + 3 * x, prove -2 / 3 ≤ x ∧ x ≤ 0
    intro h_eq
    have h1 : Real.sqrt ((2 - 3 * abs x) ^ 2) = abs (2 - 3 * abs x) := by
      rw [Real.sqrt_sq_eq_abs]
    rw [h1] at h_eq
    by_cases h2 : (2 - 3 * abs x) ≥ 0
    · -- case 1, 2 - 3 * abs x ≥ 0
      have h3 : abs (2 - 3 * abs x) = 2 - 3 * abs x := by
        rw [abs_of_nonneg h2]
      rw [h3] at h_eq
      have h4 : -3 * abs x = 3 * x := by linarith
      by_cases h5 : x ≥ 0
      · -- x ≥ 0
        have h6 : abs x = x := abs_of_nonneg h5
        rw [h6] at h4
        have h7 : x = 0 := by linarith
        constructor
        · linarith
        · linarith
      · -- x < 0
        have h8 : abs x = -x := by
          rw [abs_of_neg (by linarith)]
        rw [h8] at h4
        have h5 : x ≤ 0 := by linarith
        have h10 : -2 / 3 ≤ x := by
          have h5' : abs x ≤ 2 / 3 := by
            nlinarith
          cases' abs_cases x with h9 h9
          · linarith
          · linarith
        constructor
        · linarith
        · linarith
    · -- case 2, 2 - 3 * abs x < 0
      have h4 : abs (2 - 3 * abs x) = (3 * abs x - 2) := by
        rw [abs_of_neg (by linarith)]
        all_goals linarith
      rw [h4] at h_eq
      by_cases h5 : x ≥ 0
      · -- x ≥ 0
        have h6 : abs x = x := abs_of_nonneg h5
        rw [h6] at h_eq
        linarith
      · -- x < 0
        have h7 : abs x = -x := by
          rw [abs_of_neg (by linarith)]
        rw [h7] at h_eq
        have h8 : x = -2 / 3 := by linarith
        constructor
        · linarith
        · linarith
  · -- Assume -2 / 3 ≤ x ∧ x ≤ 0, prove Real.sqrt ((2 - 3 * abs x) ^ 2) = 2 + 3 * x
    rintro ⟨h1, h2⟩
    have h3 : abs x = -x := by
      rw [abs_of_nonpos (by linarith)]
    have h4 : 2 - 3 * abs x ≥ 0 := by
      rw [h3]
      nlinarith
    have h5 : Real.sqrt ((2 - 3 * abs x) ^ 2) = abs (2 - 3 * abs x) := by
      rw [Real.sqrt_sq_eq_abs]
    rw [h5]
    have h6 : abs (2 - 3 * abs x) = (2 - 3 * abs x : ℝ) := by
      rw [abs_of_nonneg h4]
    rw [h6]
    have h7 : abs x = -x := by
      rw [abs_of_nonpos (by linarith)]
    rw [h7]
    nlinarith