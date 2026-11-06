import Mathlib

open Real

theorem algebra_267549 (k : ℝ) (hk : k > 0) :
    IsGreatest {x | ∃ a b, a ≥ 0 ∧ b ≥ 0 ∧ a + b = k ∧ x = sqrt a + sqrt b} (sqrt (k / 2) + sqrt (k / 2)) := by
  constructor
  · -- Show that sqrt (k / 2) + sqrt (k / 2) is in the set
    use k / 2, k / 2
    constructor
    · -- Show that k / 2 ≥ 0
      linarith
    constructor
    · -- Show that k / 2 ≥ 0
      linarith
    constructor
    · -- Show that k / 2 + k / 2 = k
      linarith
    · -- Show that sqrt (k / 2) + sqrt (k / 2) = sqrt (k / 2) + sqrt (k / 2)
      rfl
  · -- Show that sqrt (k / 2) + sqrt (k / 2) is the greatest element in the set
    intro x hx
    rcases hx with ⟨a, b, ha, hb, h_eq_k, hx_eq⟩
    have h1 : sqrt a + sqrt b ≤ sqrt (k / 2) + sqrt (k / 2) := by
      have h1 : (sqrt a + sqrt b) ^ 2 ≤ (sqrt (k / 2) + sqrt (k / 2)) ^ 2 := by
        have h2 : (sqrt a + sqrt b) ^ 2 = (sqrt a) ^ 2 + (sqrt b) ^ 2 + 2 * (sqrt a * sqrt b) := by
          ring
        have h3 : (sqrt (k / 2) + sqrt (k / 2)) ^ 2 = (sqrt (k / 2)) ^ 2 + (sqrt (k / 2)) ^ 2 + 2 * (sqrt (k / 2) * sqrt (k / 2)) := by
          ring
        have h4 : (sqrt a) ^ 2 = a := by
          rw [Real.sq_sqrt]
          linarith
        have h5 : (sqrt b) ^ 2 = b := by
          rw [Real.sq_sqrt]
          linarith
        have h6 : (sqrt (k / 2)) ^ 2 = k / 2 := by
          rw [Real.sq_sqrt]
          linarith
        rw [h2, h3, h4, h5, h6]
        nlinarith [sq_nonneg (sqrt a - sqrt b), sq_nonneg (sqrt (k / 2) - sqrt (k / 2)), 
          sq_nonneg (a - b), 
          Real.sqrt_nonneg (k / 2),
          Real.sq_sqrt (show (k / 2 : ℝ) ≥ 0 by linarith),
          mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b),
          sq_nonneg (sqrt a * sqrt b - (k / 2)), 
          Real.sqrt_nonneg (a * b), 
          mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ b by linarith), 
          sq_nonneg (a - k / 2), sq_nonneg (b - k / 2)
        ]
      nlinarith [Real.sqrt_nonneg (k / 2), Real.sqrt_nonneg (k / 2), 
        Real.sqrt_nonneg a, Real.sqrt_nonneg b, 
        sq_nonneg (sqrt a + sqrt b - (sqrt (k / 2) + sqrt (k / 2))), 
        Real.sq_sqrt (show (k / 2 : ℝ) ≥ 0 by linarith), 
        Real.sq_sqrt (show (k / 2 : ℝ) ≥ 0 by linarith), 
        Real.sq_sqrt (show (a : ℝ) ≥ 0 by linarith), 
        Real.sq_sqrt (show (b : ℝ) ≥ 0 by linarith)
      ]
    have hx_eq' : x = sqrt a + sqrt b := by
      linarith [hx_eq]
    linarith [hx_eq', h1]