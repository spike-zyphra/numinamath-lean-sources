import Mathlib

theorem algebra_327659 (x y : ℤ) (hx : 0 < x) (hy : 0 < y)
    (h1 : x * y + x + y = 71) (h2 : x ^ 2 * y + x * y ^ 2 = 880) :
    x ^ 2 + y ^ 2 = 146 := by
  have eq3 : x * y * (x + y) = 880 := by
    linarith [h2]
  have eq4 : x * y = 71 - (x + y) := by
    linarith [h1]
  rw [eq4] at eq3
  have h4 : (x + y : ℤ) ^ 2 - 71 * (x + y) + 880 = 0 := by
    nlinarith
  have h5 : (x + y : ℤ) = 55 ∨ (x + y : ℤ) = 16 := by
    have h6 : (x + y : ℤ) ^ 2 - 71 * (x + y) + 880 = 0 := h4
    have h7 : (x + y : ℤ) ^ 2 - 71 * (x + y) + 880 = (x + y - 55) * (x + y - 16) := by
      ring
    rw [h7] at h6
    cases (mul_eq_zero.mp h6) with
    | inl h9 =>
      left
      linarith
    | inr h10 =>
      right
      linarith
  rcases h5 with h5 | h5
  · -- Case $x + y = 55$
    have h6 : x + y = 55 := by linarith
    have h7 : x * y = 16 := by 
      nlinarith
    nlinarith [sq_nonneg (x - y), sq_nonneg (x * y - 16), sq_nonneg (x + y - 55), mul_pos hx hy]
  · -- Case $x + y = 16$
    have h8 : x + y = 16 := by linarith
    have h9 : x * y = 55 := by
      nlinarith
    have h10 : x ≤ 16 := by nlinarith
    have h11 : y ≤ 16 := by nlinarith
    have h12 : x = 5 ∨ x = 11 := by
      interval_cases x <;> omega
    rcases h12 with h13 | h14
    · -- Case $x = 5$
      have h15 : y = 11 := by
        nlinarith
      rw [h13, h15]
      norm_num
    · -- Case $x = 11$
      have h16 : y = 5 := by
        nlinarith
      rw [h14, h16]
      norm_num