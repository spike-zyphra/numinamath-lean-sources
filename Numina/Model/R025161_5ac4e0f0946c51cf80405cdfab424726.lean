import Mathlib

open Real

theorem inequalities_600125 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hsum : x + y + z = 1) :
    x * y + y * z + z * x ≥ 4 * (x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2) +
      5 * x * y * z ∧
    (x * y + y * z + z * x = 4 * (x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2) + 5 * x * y * z ↔
      (x = y ∧ y = z)) := by
  constructor
  · -- First, prove the inequality.
    have h1 : z = 1 - x - y := by linarith
    rw [h1]
    have h2 : x * y + y * (1 - x - y) + (1 - x - y) * x ≥ 4 * (x ^ 2 * y ^ 2 + y ^ 2 * (1 - x - y) ^ 2 + (1 - x - y) ^ 2 * x ^ 2) + 5 * x * y * (1 - x - y) := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - (1 - x - y)), sq_nonneg (y - (1 - x - y)), 
          mul_pos hx hy, mul_pos hx (show (0 : ℝ) < 1 - x - y by nlinarith), 
          mul_pos hy (show (0 : ℝ) < 1 - x - y by nlinarith)
        ]
    linarith
  · -- Second, prove the equality condition
    constructor
    · -- Forward direction of biimplication: equality holds, then variables equal
      intro heq
      -- Now have the equality. z =1 -x -y.
      have h1 : z = 1 - x - y := by linarith
      rw [h1] at heq
      have h2 : (x - y) ^ 2 = 0 := by
        nlinarith [sq_nonneg (x - y), sq_nonneg (x - (1 - x - y)), sq_nonneg (y - (1 - x - y)), 
            mul_pos hx hy, mul_pos hx (show 0 < (1 - x - y : ℝ) by nlinarith), 
            mul_pos hy (show 0 < (1 - x - y : ℝ) by nlinarith)
          ]
      have h3 : x - y = 0 := by 
        nlinarith
      have h4 : x = y := by linarith
      have h5 : (y - (1 - x - y)) ^ 2 = 0 := by
        nlinarith [sq_nonneg (x - y), sq_nonneg (y - (1 - x - y)), sq_nonneg (x - (1 - x - y)), 
            mul_pos hx hy, mul_pos hx (show 0 < (1 - x - y : ℝ) by nlinarith), 
            mul_pos hy (show 0 < (1 - x - y : ℝ) by nlinarith)
          ]
      have h8 : y = (1 - x - y) := by nlinarith
      have h10 : z = y := by
        have h1' : z = 1 - x - y := by linarith
        have h11 : 1 - x - y = y := by linarith
        linarith [h1', h11]
      constructor
      · linarith
      · linarith
    · -- Backward direction: variables equal implies equality
      rintro ⟨hx1, hy1⟩
      have h4 : x = y := by linarith
      have h5 : y = z := by linarith
      have h6 : x = z := by linarith
      -- Rewrite all variables in terms of x.
      rw [show y = x by linarith] 
      rw [show z = x by linarith]
      nlinarith