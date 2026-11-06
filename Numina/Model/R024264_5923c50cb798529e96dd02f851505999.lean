import Mathlib

theorem algebra_166186 {x y z : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (h1 : (x ^ 3 / (x + 26 : ℚ)) = (y / (y + 25 : ℚ))) (h2 : (y / (y + 25 : ℚ)) = (z ^ 2 / (z + 12 : ℚ))) :
    x = 2 ∧ y = 10 ∧ z = 2 := by
  have eq1 : (x : ℚ) ^ 3 * (y + 25 : ℚ) = (y : ℚ) * (x + 26 : ℚ) := by
    have denom1 : (x + 26 : ℚ) ≠ 0 := by
      have h : (x : ℚ) ≠ 0 := by exact_mod_cast hx
      have hx2 : (x : ℚ) > 0 := by
        have h : (x : ℚ) > 0 := by positivity
        nlinarith
      nlinarith
    have denom2 : (y + 25 : ℚ) ≠ 0 := by
      have hy2 : (y : ℚ) > 0 := by
        have h : (y : ℚ) > 0 := by positivity
        nlinarith
      nlinarith
    field_simp [denom1, denom2] at h1 ⊢
    nlinarith
  have eq2 : (y : ℚ) * (z + 12 : ℚ) = (z : ℚ) ^ 2 * (y + 25 : ℚ) := by
    have denom3 : (y + 25 : ℚ) ≠ 0 := by
      have hy2 : (y : ℚ) > 0 := by
        have h : (y : ℚ) > 0 := by positivity
        nlinarith
      nlinarith
    have denom4 : (z + 12 : ℚ) ≠ 0 := by
      have h : (z : ℚ) ≠ 0 := by exact_mod_cast hz
      have hz2 : (z : ℚ) > 0 := by
        have h : (z : ℚ) > 0 := by positivity
        nlinarith
      nlinarith
    field_simp [denom3, denom4] at h2 ⊢
    nlinarith
  have eq3 : x ^ 3 * (y + 25) = y * (x + 26) := by
    exact_mod_cast eq1
  have eq4 : y * (z + 12) = z ^ 2 * (y + 25) := by
    exact_mod_cast eq2
  have h3 : x ≤ 3 := by
    nlinarith [sq_nonneg (x ^ 2 : ℕ), sq_nonneg (x : ℕ), sq_nonneg (y : ℕ), sq_nonneg (x - 3 : ℤ), sq_nonneg (y - 10 : ℤ), mul_pos (show (x : ℕ) > 0 by omega) (show (y : ℕ) > 0 by omega)]
  have h4 : z ≤ 3 := by
    nlinarith [sq_nonneg (z ^ 2 : ℕ), sq_nonneg (z : ℕ), sq_nonneg (y : ℕ), sq_nonneg (z - 3 : ℤ), sq_nonneg (y - 10 : ℤ), mul_pos (show (z : ℕ) > 0 by omega) (show (y : ℕ) > 0 by omega)]
  have hx2 : x = 1 ∨ x = 2 ∨ x = 3 := by
    omega
  have h6 : z = 1 ∨ z = 2 ∨ z = 3 := by
    omega
  rcases hx2 with (h | h | h)
  · -- x = 1
    rw [show x = 1 by omega] at eq3
    omega
  · -- x = 2
    rw [show x = 2 by omega] at eq3
    rcases h6 with (h | h | h)
    · -- z = 1
      rw [show z = 1 by omega] at eq4
      all_goals omega
    · -- z = 2
      rw [show z = 2 by omega] at eq4
      have hy10 : y = 10 := by
        nlinarith
      simp [hy10]
      all_goals tauto
    · -- z = 3
      rw [show z = 3 by omega] at eq4
      all_goals omega
  · -- x = 3
    rw [show x = 3 by omega] at eq3
    all_goals omega