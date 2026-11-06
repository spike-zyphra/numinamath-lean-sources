import Mathlib

theorem algebra_8216 {x : ℝ} (hx : x^2 - x - 1 = 0) (hx2 : x ≠ 0) : x^8 + 7 / x^4 = 48 := by
  have h1 : x^2 = x + 1 := by linarith
  have h2 : x^3 = 2 * x + 1 := by
    calc
      x^3 = x * x^2 := by ring
      _ = x * (x + 1) := by rw [h1]
      _ = x^2 + x := by ring
      _ = (x + 1) + x := by rw [h1]
      _ = 2 * x + 1 := by ring
  have h3 : x^4 = 3 * x + 2 := by
    calc
      x^4 = x * x^3 := by ring
      _ = x * (2 * x + 1) := by rw [h2]
      _ = 2 * x^2 + x := by ring
      _ = 2 * (x + 1) + x := by rw [h1]
      _ = 2 * x + 2 + x := by ring
      _ = 3 * x + 2 := by ring
  have h4 : x^8 = 21 * x + 13 := by
    calc
      x^8 = (x^4) ^ 2 := by ring
      _ = (3 * x + 2) ^ 2 := by rw [h3]
      _ = 9 * x^2 + 12 * x + 4 := by ring
      _ = 9 * (x + 1) + 12 * x + 4 := by rw [h1]
      _ = 9 * x + 9 + 12 * x + 4 := by ring
      _ = 21 * x + 13 := by ring
  have h5 : 1 / x = x - 1 := by
    have h51 : x - 1 / x = 1 := by
      have h6 : x^2 - x - 1 = 0 := by linarith
      have h7 : x ≠ 0 := hx2
      field_simp [h7] at *
      nlinarith
    field_simp [hx2] at h51 ⊢
    linarith
  have h6 : 1 / x^4 = 5 - 3 * x := by
    have h7 : 1 / x^4 = (1 / x) ^ 4 := by field_simp [hx2]
    rw [h7]
    have h8 : (1 / x) ^ 4 = (x - 1) ^ 4 := by
      rw [h5]
      all_goals ring
    rw [h8]
    have h9 : (x - 1) ^ 4 = 5 - 3 * x := by
      have h91 : (x - 1) ^ 2 = 2 - x := by
        nlinarith [h1]
      calc
        (x - 1) ^ 4 = ((x - 1) ^ 2) ^ 2 := by ring
        _ = (2 - x) ^ 2 := by rw [h91]
        _ = 4 - 4 * x + x^2 := by ring
        _ = 4 - 4 * x + (x + 1) := by rw [h1]
        _ = 5 - 3 * x := by ring
    linarith [h9]
  have h71 : 7 / x^4 = 7 * (5 - 3 * x) := by
    have h81 : 7 / x^4 = 7 * (1 / x^4) := by
      field_simp [hx2]
      <;> ring
    rw [h81, h6]
    all_goals ring
  rw [h71]
  rw [h4]
  all_goals nlinarith [sq_nonneg (x - 1), sq_nonneg (x - (1 / 2)), sq_nonneg (x^2 - 1), sq_nonneg (x - 2)]