import Mathlib

theorem algebra_102287 {a b : ℤ} (ha : a > 0) (hb : b > 0)
    (h : a^2 + 2 * a * b - 3 * b^2 - 41 = 0) : a^2 + b^2 = 221 := by
  have h1 : (a - b) * (a + 3 * b) = 41 := by
    nlinarith
  have h2 : (a - b) * (a + 3 * b) = 41 := h1
  have h3 : (a - b) ∣ 41 := by
    use (a + 3 * b)
    all_goals nlinarith
  have h4 : (a - b) = 1 ∨ (a - b) = 41 ∨ (a - b) = -1 ∨ (a - b) = -41 := by
    have h5 : (a - b) ∣ 41 := h3
    have h6 : (a - b) ≤ 41 := by
      apply Int.le_of_dvd (by norm_num) h5
    have h7 : (a - b) ≥ -41 := by
      have h8 : (- (a - b)) ∣ 41 := by
        exact Int.neg_dvd.2 h5
      have h9 : - (a - b) ≤ 41 := by
        apply Int.le_of_dvd (by norm_num) h8
      linarith
    interval_cases (a - b) <;> tauto
  rcases h4 with (h4 | h4 | h4 | h4)
  · -- a - b = 1
    have h5 : a + 3 * b = 41 := by
      rw [h4] at h1
      linarith
    have h6 : b = 10 := by
      linarith
    have h7 : a = 11 := by 
      linarith
    rw [h7, h6]
    norm_num
  · -- a - b = 41
    have h5 : a + 3 * b = 1 := by
      rw [h4] at h1
      linarith
    have h6 : b < (0 : ℤ) := by
      nlinarith
    linarith
  · -- a - b = -1
    have h5 : a + 3 * b = -41 := by
      rw [h4] at h1
      linarith
    have h6 : b < (0 : ℤ) := by
      nlinarith
    linarith
  · -- a - b = -41
    have h5 : a + 3 * b = -1 := by
      rw [h4] at h1
      linarith
    have h6 : a < (0 : ℤ) := by 
      nlinarith
    linarith