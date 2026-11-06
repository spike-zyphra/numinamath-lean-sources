import Mathlib

theorem algebra_107297 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (x : ℝ) (hx : b^2 ≤ x) (hy : a^2 ≤ x) :
    Real.sqrt (x - b^2) - Real.sqrt (x - a^2) = a - b ↔ x = a^2 + b^2 := by
  constructor
  · -- Forward: Assume sqrt(x - b²) - sqrt(x - a²) = a - b prove x = a² + b²
    intro h_eq
    have h1 : Real.sqrt (x - b^2) = a - b + Real.sqrt (x - a^2) := by linarith
    have h2 : Real.sqrt (x - b^2) = a - b + Real.sqrt (x - a^2) := by linarith
    have h3 : Real.sqrt (x - b^2) ^ 2 = (a - b + Real.sqrt (x - a^2)) ^ 2 := by
      rw [h2]
    have h4 : Real.sqrt (x - b^2) ^ 2 = x - b^2 := Real.sq_sqrt (by linarith)
    have h5 : (a - b + Real.sqrt (x - a^2)) ^ 2 = (a - b) ^ 2 + 2 * (a - b) * Real.sqrt (x - a^2) + (Real.sqrt (x - a^2) ^ 2) := by
      ring
    have h6 : Real.sqrt (x - a^2) ^ 2 = x - a^2 := Real.sq_sqrt (by linarith)
    rw [h4, h5, h6] at h3
    have h7 : Real.sqrt (x - a^2) = b := by
      -- Use linarith by manipulating the existing equations.
      -- When expanding (√(x - b²))², we get x - b².
      -- When expanding (√(x - a²) + a - b)², we need to find terms canceling.
      -- By correctly manipulating terms, we get an equation of the form:
      -- √(x - a²) = b
      -- Square both sides to get:
      -- x - a² = b²
      -- Therefore x = a² + b²
      have h8 : 0 < a := ha
      have h9 : 0 < b := hb
      have h10 : a ≠ b := hab
      nlinarith [sq_nonneg (Real.sqrt (x - a^2) - b), sq_nonneg (a - b),
        h_eq, Real.sqrt_nonneg (x - b^2), Real.sqrt_nonneg (x - a^2),
        Real.sq_sqrt (show (0 : ℝ) ≤ x - a^2 by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ x - b^2 by linarith),
        sq_pos_of_ne_zero (show a - b ≠ 0 by intro h; apply hab; linarith)]
    -- By proving √(x - a²) = b
    -- We can square both sides to get x - a² = b²
    -- Therefore x = a² + b²
    have h8 : Real.sqrt (x - a^2) ^ 2 = b ^ 2 := by
      rw [h7]
      all_goals nlinarith
    -- This gives us x - a² = b²
    have h9 : x - a^2 = b ^ 2 := by
      linarith [show Real.sqrt (x - a^2) ^ 2 = x - a^2 by apply Real.sq_sqrt; linarith, h8]
    -- Therefore x = a² + b²
    linarith
  · -- Backward: Assume x = a² + b² prove sqrt(x - b²) - sqrt(x - a²) = a - b
    intro h_eq
    rw [h_eq]
    have h1 : Real.sqrt ((a ^ 2 + b ^ 2) - b ^ 2) = Real.sqrt (a ^ 2) := by
      ring_nf
      all_goals try { 
        nlinarith 
      }
    have h2 : Real.sqrt ((a ^ 2 + b ^ 2) - a ^ 2) = Real.sqrt (b ^ 2) := by
      ring_nf
      all_goals try { 
        nlinarith 
      }
    have h3 : Real.sqrt (a ^ 2) = a := Real.sqrt_sq (show 0 ≤ a by linarith)
    have h4 : Real.sqrt (b ^ 2) = b := Real.sqrt_sq (show 0 ≤ b by linarith)
    rw [h1, h3, h2, h4]
    all_goals try { 
      nlinarith 
    }