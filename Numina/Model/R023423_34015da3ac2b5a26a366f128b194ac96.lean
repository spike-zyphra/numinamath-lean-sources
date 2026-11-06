import Mathlib

theorem algebra_188165 {x y z : ℝ} (h1 : x^2 - y * z = 3) (h2 : y^2 - x * z = 4) (h3 : z^2 - x * y = 5) :
    (x, y, z) = (11 / 6, -1 / 6, -13 / 6) ∨ (x, y, z) = (-11 / 6, 1 / 6, 13 / 6) := by

  have eq1 : (y - x) * (x + y + z) = 1 := by
    nlinarith

  have eq2 : (z - y) * (x + y + z) = 1 := by
    nlinarith

  by_cases h : x + y + z = 0
  · -- Case where x + y + z = 0
    have h4 : z = -x - y := by linarith
    rw [h4] at h1 h2 h3
    nlinarith

  · -- x + y + z ≠ 0
    have h4 : y - x = z - y := by
      apply (mul_left_inj' h).mp
      linarith
    have h5 : z = 2 * y - x := by linarith
    rw [h5] at h1 h2 h3
    have h4 : (x - y) ^ 2 = 4 := by
      nlinarith
    have h5 : x - y = 2 ∨ x - y = -2 := by 
      have h1 : (x - y) ^ 2 - 4 = 0 := by linarith
      have h2 : (x - y - 2) * (x - y + 2) = 0 := by 
        nlinarith
      cases (mul_eq_zero.1 h2) with
      | inl h => 
        left
        linarith
      | inr h => 
        right
        linarith

    cases h5 with
    | inl h6 => 
      have h9 : x = y + 2 := by linarith
      rw [h9] at h1 h2 h3
      have h61 : y = -1 / 6 := by 
        nlinarith
      have h62 : x = 11 / 6 := by
        linarith [h61, h9]
      have h63 : z = -13 / 6 := by 
        nlinarith [h61, h62, h5]
      left
      simp [h62, h61, h63]
    | inr h6 => 
      have h9 : x = y - 2 := by linarith
      rw [h9] at h1 h2 h3
      have h61 : y = 1 / 6 := by 
        nlinarith
      have h62 : x = -11 / 6 := by
        linarith [h61, h9]
      have h63 : z = 13 / 6 := by 
        nlinarith [h61, h62, h5]
      right
      simp [h62, h61, h63]