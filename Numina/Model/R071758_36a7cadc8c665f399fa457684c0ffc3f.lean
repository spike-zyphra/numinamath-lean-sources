import Mathlib

theorem algebra_926 {x : ℝ} (hx : x^2 - x - 1 = 0) (hx2 : x ≠ 0) : (x^3 + x + 1) / x^4 = 1 := by
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
      x^4 = (x^2) ^ 2 := by ring
      _ = (x + 1) ^ 2 := by rw [h1]
      _ = x^2 + 2 * x + 1 := by ring
      _ = (x + 1) + 2 * x + 1 := by rw [h1]
      _ = 3 * x + 2 := by ring
  have h4 : x^3 + x + 1 = 3 * x + 2 := by
    rw [h2]
    linarith
  have h5 : x^4 ≠ 0 := by
    intro h
    have h6 : x^4 = 0 := by linarith
    have h7 : x = 0 := by
      have h8 : x^4 = 0 := by linarith
      have h9 : x = 0 := by
        have h10 : x^4 = 0 := by linarith
        simp at h10 ⊢
        <;> nlinarith
      exact h9
    contradiction
  have h6 : 3 * x + 2 ≠ 0 := by
    by_contra h
    have h7 : x = -2 / 3 := by linarith
    rw [h7] at hx
    norm_num at hx
  have h8 : (x^3 + x + 1) / x^4 = 1 := by
    rw [show (x^3 + x + 1) = x^4 by linarith [h4, h3]]
    field_simp [h5, h6]
    <;> nlinarith
  exact h8