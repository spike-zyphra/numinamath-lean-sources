import Mathlib

theorem number_theory_169980 : ¬∃ x y : ℤ, x > 0 ∧ y > 0 ∧ x ^ 3 + 11 ^ 3 = y ^ 3 := by
  rintro ⟨x, y, hx, hy, heq⟩
  have h1 : y > x := by
    nlinarith [sq_nonneg (y - x), sq_nonneg (y + x), sq_nonneg (x - 11), sq_nonneg (y - 11), sq_nonneg (y^2 - x^2)]
  have h2 : y - x ∣ 11 ^ 3 := by
    use y ^ 2 + y * x + x ^ 2
    nlinarith [heq]
  have h3 : y - x = 1 ∨ y - x = 11 ∨ y - x = 121 ∨ y - x = 1331 := by
    have h4 : y - x ∣ 11 ^ 3 := h2
    have h5 : y - x > 0 := by
      omega
    have h6 : y - x ≤ 11 ^ 3 := by
      apply Int.le_of_dvd (by norm_num) h4
    interval_cases k : y - x <;> norm_num at h4 <;> tauto
  rcases h3 with (h | h | h | h)
  · -- y - x = 1
    have h4 : y = x + 1 := by
      linarith
    rw [h4] at heq
    ring_nf at heq
    have h7 : 3 * x ^ 2 + 3 * x + 1 = 1331 := by
      nlinarith
    have h8 : 3 * x ^ 2 + 3 * x - 1330 = 0 := by
      nlinarith
    have h9 : x ≤ 21 := by
      nlinarith [sq_nonneg (3 * x + 1)]
    have h10 : x ≥ -22 := by
      nlinarith [sq_nonneg (3 * x + 1)]
    interval_cases x <;> omega
  · -- y - x = 11
    have h4 : y = x + 11 := by
      linarith
    rw [h4] at heq
    ring_nf at heq
    have h7 : 33 * x ^ 2 + 363 * x = 0 := by
      nlinarith
    have h9 : 33 * (x) * (x + 11) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h9) with h10 h11
    · -- 33 * x = 0
      have h12 : x = 0 := by
        nlinarith
      linarith
    · -- x + 11 = 0
      have h13 : x = -11 := by
        nlinarith
      linarith
  · -- y - x = 121
    have h4 : y = x + 121 := by
      linarith
    rw [h4] at heq
    ring_nf at heq
    nlinarith [sq_nonneg (x + 11), sq_nonneg (x + 121), sq_nonneg (x ^ 2 + 11 * x + 121), sq_nonneg (y ^ 2 - x ^ 2)]
  · -- y - x = 1331
    have h4 : y = x + 1331 := by
      linarith
    rw [h4] at heq
    ring_nf at heq
    nlinarith [sq_nonneg (x + 11), sq_nonneg (x + 1331), sq_nonneg (x ^ 2 + 11 * x + 121), sq_nonneg (y ^ 2 - x ^ 2)]