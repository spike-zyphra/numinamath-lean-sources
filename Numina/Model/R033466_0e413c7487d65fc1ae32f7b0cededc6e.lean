import Mathlib

theorem algebra_167967 {x y : ℝ} (hx : x > 0) (hxy : x ^ (y ^ 2 - 7 * y + 10) = 1 ∧ x + y = 8) :
    (x, y) = (1, 7) ∨ (x, y) = (6, 2) ∨ (x, y) = (3, 5) := by
  rcases hxy with ⟨h1, h2⟩
  have h3 : y = 8 - x := by linarith
  rw [h3] at h1
  have h5 : ((8 - x) ^ 2 - 7 * (8 - x) + 10 : ℝ) = (x^2 - 9 * x + 18 : ℝ) := by
    ring_nf
  rw [h5] at h1
  have h7 : x = 1 ∨ (x ^ 2 - 9 * x + 18) = 0 := by
    by_cases h : x = 1
    · left
      exact h
    · -- Assume x ≠ 1, prove the exponent is 0
      right
      have h8 : x ^ (x ^ 2 - 9 * x + 18) = 1 := h1
      have h9 : x ^ 2 - 9 * x + 18 = 0 := by
        have h10 : x ^ (x ^ 2 - 9 * x + 18) = 1 := h8
        have h11 : (x ^ (x ^ 2 - 9 * x + 18) : ℝ) = 1 := by linarith
        have h12 : (x ^ 2 - 9 * x + 18 : ℝ) * (Real.log x) = 0 := by
          calc
            (x ^ 2 - 9 * x + 18 : ℝ) * (Real.log x)
                = (Real.log ((x : ℝ) ^ (x ^ 2 - 9 * x + 18 : ℝ))) := by 
                  rw [Real.log_rpow]
                  all_goals nlinarith
            _ = (Real.log (1 : ℝ)) := by
              rw [h11]
            _ = (0 : ℝ) := by
              simp
        cases' (mul_eq_zero.mp h12) with h13 h14
        · -- h13 : (x ^ 2 - 9 * x + 18 : ℝ) = 0
          linarith
        · -- h14 : (Real.log x) = 0
          have h15 : x = 1 := by
            rw [Real.log_eq_zero] at h14
            rcases h14 with (r | r | r)
            · linarith
            · linarith
            · linarith
          exfalso
          exact h (h15)
      linarith
  cases h7 with
  | inl h8 =>
    left
    have hx1 : x = 1 := h8
    have hy1 : y = 7 := by
      linarith [h2, hx1]
    simp [hx1, hy1]
    <;> norm_num
  | inr h8 =>
    have h10 : (x - 3) * (x - 6) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h10) with h11 h12
    · -- x = 3
      have hx2 : x = 3 := by
        linarith
      have hy2 : y = 5 := by
        linarith [h2, hx2]
      simp [hx2, hy2]
      <;> norm_num
    · -- x = 6
      have hx3 : x = 6 := by
        linarith
      have hy3 : y = 2 := by
        linarith [h2, hx3]
      simp [hx3, hy3]
      <;> norm_num