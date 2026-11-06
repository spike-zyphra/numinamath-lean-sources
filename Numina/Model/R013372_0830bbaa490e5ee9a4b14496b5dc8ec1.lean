import Mathlib

theorem algebra_179621 {a q1 q2 : ℝ} (hq1 : |q1| < 1) (hq2 : |q2| < 1)
    (h : q1 = -q2) (S1 S2 : ℝ) (hS1 : S1 = a / (1 - q1)) (hS2 : S2 = a / (1 - q2)) :
    ∑' n : ℕ, (a * q1 ^ n) ^ 2 = S1 * S2 := by
  have hq12 : |q1^2| < 1 := by
    have h1 : |q1| < 1 := hq1
    have h2 : |q1^2| = |q1| ^ 2 := by
      simp [abs_pow]
    rw [h2]
    have h3 : |q1| < 1 := h1
    have h4 : |q1| ^ 2 < (1 : ℝ) := by
      nlinarith [abs_nonneg q1, h3]
    linarith
  have h5 : ∑' n : ℕ, (a * q1 ^ n) ^ 2 = a^2 / (1 - q1^2) := by
    have h6 : ∀ n : ℕ, (a * q1 ^ n) ^ 2 = a^2 * (q1^2) ^ n := by
      intro n
      ring_nf
    rw [tsum_congr h6]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one]
    · ring
    · simpa using hq12
  rw [h5, hS1, hS2]
  have h8 : q2 = -q1 := by
    linarith [h]
  have h7 : (1 - q1 ^ 2) = (1 - q1) * (1 - q2) := by
    rw [show q2 = -q1 by linarith [h8]]
    ring
  rw [h7]
  field_simp [(show (1 - q1) ≠ 0 by
    by_contra h1
    have h2 : q1 = 1 := by linarith
    have h3 : |q1| = 1 := by
      rw [h2]
      norm_num
    linarith [hq1, h3]
  ), (show (1 - q2) ≠ 0 by
    by_contra h1
    have h2 : q2 = 1 := by linarith
    have h3 : |q2| = 1 := by
      rw [h2]
      norm_num
    linarith [hq2, h3]
  )
  ]
  <;> ring