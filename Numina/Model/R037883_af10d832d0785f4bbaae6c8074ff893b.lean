import Mathlib

open Real

theorem algebra_287733 {a b c : ℝ} (ha : 0 < c) (hc : c < b) (hb : b < a)
    (l1 l2 l3 : ℝ) (hl1 : l1 = sqrt ((a + c)^2 + b^2)) (hl2 : l2 = sqrt (a^2 + (b + c)^2))
    (hl3 : l3 = sqrt ((a + b)^2 + c^2)) :
    min (min (min (min (l1 * l2) (l1 * l3)) (l2 * l3)) (l2^2)) (l3^2) = l2^2 := by
  have h1 : l1 = sqrt ((a + c)^2 + b^2) := by exact hl1
  have h2 : l2 = sqrt (a^2 + (b + c)^2) := by exact hl2
  have h3 : l3 = sqrt ((a + b)^2 + c^2) := by exact hl3
  have h4 : l2 ^ 2 = a^2 + (b + c)^2 := by
    rw [h2]
    rw [Real.sq_sqrt]
    positivity
  have h8 : l3^2 = (a + b)^2 + c^2 := by
    rw [h3]
    rw [Real.sq_sqrt]
    positivity
  -- show l1 ≥ l2 
  have h9 : l2^2 ≤ l1 * l2 := by
    have h11 : l1 * l2 = Real.sqrt ((a + c)^2 + b^2) * Real.sqrt (a^2 + (b + c)^2) := by
      rw [h1, h2]
    have h12 : Real.sqrt ((a + c)^2 + b^2) * Real.sqrt (a^2 + (b + c)^2) ≥ Real.sqrt (a^2 + (b + c)^2) ^ 2 := by
      have h131 : Real.sqrt ((a + c)^2 + b^2) ≥ 0 := Real.sqrt_nonneg ((a + c)^2 + b^2)
      have h133 : Real.sqrt (a^2 + (b + c)^2) ≥ 0 := Real.sqrt_nonneg (a^2 + (b + c)^2)
      have h134 : Real.sqrt ((a + c)^2 + b^2) ≥ Real.sqrt (a^2 + (b + c)^2) := by
        apply Real.sqrt_le_sqrt
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c), mul_pos ha (show 0 < b by linarith)]
      nlinarith [Real.sqrt_nonneg ((a + c)^2 + b^2), Real.sqrt_nonneg (a^2 + (b + c)^2), Real.sq_sqrt (show (0: ℝ) ≤ (a ^ 2 + (b + c) ^ 2 : ℝ) by positivity), Real.sq_sqrt (show (0: ℝ) ≤ ((a + c) ^ 2 + b ^ 2 : ℝ) by positivity), mul_nonneg (Real.sqrt_nonneg ((a + c)^2 + b^2)) (Real.sqrt_nonneg (a^2 + (b + c)^2))]
    have h14 : Real.sqrt ((a + c) ^ 2 + b^2) * Real.sqrt (a^2 + (b + c) ^ 2) = l1 * l2 := by
      rw [h11]
    have h14300 : Real.sqrt (a^2 + (b + c)^2) ^ 2 = a^2 + (b + c) ^ 2 := by
      rw [Real.sq_sqrt (show (0 : ℝ) ≤ (a ^ 2 + (b + c) ^ 2 : ℝ) by positivity)]
    nlinarith
  -- Show l2^2 ≤ l1 * l3
  have h10 : l2^2 ≤ l1 * l3 := by
    have h110 : l1 * l3 = Real.sqrt ((a + c)^2 + b^2) * Real.sqrt ((a + b)^2 + c^2) := by
      rw [h1, h3]
    have h120 : Real.sqrt ((a + c)^2 + b^2) * Real.sqrt ((a + b)^2 + c^2) ≥ Real.sqrt (a^2 + (b + c)^2) ^ 2 := by
      have h131 : Real.sqrt ((a + c)^2 + b^2) ≥ 0 := Real.sqrt_nonneg ((a + c)^2 + b^2)
      have h132 : Real.sqrt ((a + b)^2 + c^2) ≥ 0 := Real.sqrt_nonneg ((a + b)^2 + c^2)
      have h134 : Real.sqrt ((a + c)^2 + b^2) ≥ Real.sqrt (a^2 + (b + c)^2) := by
        apply Real.sqrt_le_sqrt
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c), mul_pos ha (show 0 < b by linarith)]
      have h135 : Real.sqrt ((a + b)^2 + c^2) ≥ Real.sqrt (a^2 + (b + c)^2) := by
        apply Real.sqrt_le_sqrt
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c), mul_pos ha (show 0 < b by linarith)]
      nlinarith [Real.sqrt_nonneg ((a + c)^2 + b^2), Real.sqrt_nonneg ((a + b)^2 + c^2),
          Real.sq_sqrt (show (0 : ℝ) ≤ (a ^ 2 + (b + c) ^ 2 : ℝ) by positivity), 
          Real.sq_sqrt (show (0 : ℝ) ≤ ((a + c) ^ 2 + b ^ 2 : ℝ) by positivity), 
          mul_nonneg (Real.sqrt_nonneg ((a + c)^2 + b^2)) (Real.sqrt_nonneg ((a + b)^2 + c^2))
        ]
    have h17 : Real.sqrt ((a + c)^2 + b^2) * Real.sqrt ((a + b)^2 + c^2) = l1 * l3 := by
      rw [h110]
    have h14300 : Real.sqrt (a^2 + (b + c)^2) ^ 2 = a^2 + (b + c) ^ 2 := by
      rw [Real.sq_sqrt (show (0 : ℝ) ≤ (a^2 + (b + c)^2) by positivity)]
    nlinarith
  have h11 : l2^2 ≤ l2 * l3 := by
    have h118 : l2 * l3 = Real.sqrt (a^2 + (b + c)^2) * Real.sqrt ((a + b)^2 + c^2) := by
      rw [h2, h3]
    have h106 : Real.sqrt (a^2 + (b + c)^2) * Real.sqrt ((a + b)^2 + c^2) ≥ Real.sqrt (a^2 + (b + c)^2) ^ 2 := by
      have h131 : Real.sqrt ((a + b)^2 + c^2) ≥ 0 := Real.sqrt_nonneg ((a + b)^2 + c^2)
      have h132 : Real.sqrt (a^2 + (b + c)^2) ≥ 0 := Real.sqrt_nonneg (a^2 + (b + c)^2)
      have h134 : Real.sqrt ((a + b)^2 + c^2) ≥ Real.sqrt (a^2 + (b + c)^2) := by
        apply Real.sqrt_le_sqrt
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c), mul_pos ha (show 0 < b by linarith)]
      nlinarith [Real.sqrt_nonneg (a^2 + (b + c)^2), Real.sqrt_nonneg ((a + b) ^ 2 + c^2),
          Real.sq_sqrt (show (0 : ℝ) ≤ (a^2 + (b + c)^2 : ℝ) by positivity), 
          Real.sq_sqrt (show (0 : ℝ) ≤ ((a + b) ^ 2 + c^2 : ℝ) by positivity), 
          mul_nonneg (Real.sqrt_nonneg (a^2 + (b + c)^2)) (Real.sqrt_nonneg ((a + b) ^ 2 + c^2))
        ]
    have h178 : Real.sqrt (a^2 + (b + c)^2) * Real.sqrt ((a + b) ^ 2 + c^2) = l2 * l3 := by
      rw [h118]
    have h14300 : Real.sqrt (a^2 + (b + c) ^ 2) ^ 2 = a^2 + (b + c) ^ 2 := by
      rw [Real.sq_sqrt (show (0 : ℝ) ≤ (a^2 + (b + c)^2) by positivity)]
    nlinarith
  have h12 : l2^2 ≤ l3^2 := by
    rw [h4, h8]
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c), mul_pos ha (show 0 < b by linarith)]
  -- Show l_2^2 minimum
  have h13 : min (min (min (min (l1 * l2) (l1 * l3)) (l2 * l3)) (l2^2)) (l3^2) = l2^2 := by
    have h14 : l2^2 ≤ l1 * l2 := h9
    have h15 : l2^2 ≤ l1 * l3 := h10
    have h16 : l2^2 ≤ l2 * l3 := h11
    have h17 : l2^2 ≤ l3^2 := h12
    have h18 : min (min (min (min (l1 * l2) (l1 * l3)) (l2 * l3)) (l2^2)) (l3^2) = l2^2 := by
      simp [min_eq_left_of_lt, h14, h15, h16, h17]
    exact h18
  exact h13