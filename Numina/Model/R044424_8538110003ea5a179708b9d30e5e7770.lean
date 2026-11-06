import Mathlib

open Real

theorem inequalities_597741 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    √a + 1 > √b ↔ ∀ x > 1, a * x + x / (x - 1) > b := by
  constructor
  · -- Assume √a + 1 > √b, prove ∀ x > 1, a * x + x / (x - 1) > b
    intro h
    intro x hx
    have h0 : (√a + 1) ^ 2 > b := by
      have h1 : √a + 1 > √b := h
      have h2 : (√a + 1) ^ 2 > (√b) ^ 2 := by nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, h1]
      have h3 : (√b) ^ 2 = b := Real.sq_sqrt (show (0 : ℝ) ≤ (b : ℝ) by linarith)
      nlinarith [h2, h3]
    have h0' : a * x + x / (x - 1) ≥ (√a + 1) ^ 2 := by
      have hx4 : x - 1 > 0 := by nlinarith
      have h4 : a * x ^ 2 - 2 * a * x + a - 2 * Real.sqrt a * x + 2 * Real.sqrt a + 1 ≥ 0 := by
        have h5 : a * x ^ 2 - 2 * a * x + a - 2 * Real.sqrt a * x + 2 * Real.sqrt a + 1 = (√a * (x - 1) - 1) ^ 2 := by
          have h6 : Real.sqrt a ^ 2 = a := by
            rw [Real.sq_sqrt]
            positivity
          nlinarith [Real.sqrt_nonneg a, sq_nonneg (√a * (x - 1) - 1)]
        rw [h5]
        positivity
      have h55 : a * x + x / (x - 1) - (√a + 1) ^ 2 ≥ 0 := by
        have hx4 : x - 1 > 0 := by nlinarith
        have h77 : (a * x + x / (x - 1) - (√a + 1) ^ 2) = (a * x ^ 2 - 2 * a * x + a - 2 * Real.sqrt a * x + 2 * Real.sqrt a + 1) / ((x - 1)) := by
          field_simp
          ring_nf
          <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ a by linarith), Real.sqrt_nonneg a, sq_nonneg (x - 1)]
        rw [h77]
        apply div_nonneg
        linarith [Real.sqrt_nonneg a]
        all_goals linarith
      linarith
    nlinarith
  · -- Assume ∀ x > 1, a * x + x / (x - 1) > b, prove √a + 1 > √b
    intro h
    have h1 : (√a + 1) ^ 2 > b := by
      have ha' : 0 < a := by linarith
      have h7 : √a > 0 := by positivity
      have h9 : 1 + 1 / Real.sqrt a > 1 := by
        have h7' : Real.sqrt a > 0 := by positivity
        have h10 : 1 / Real.sqrt a > 0 := by positivity
        linarith
      have h10 : a * (1 + 1 / Real.sqrt a) + (1 + 1 / Real.sqrt a) / ((1 + 1 / Real.sqrt a) - 1) > b := by
        apply h (1 + 1 / Real.sqrt a) 
        linarith
      have h77 : a * (1 + 1 / Real.sqrt a) + (1 + 1 / Real.sqrt a) / ((1 + 1 / Real.sqrt a) - 1) = (√a + 1) ^ 2 := by
        have h21 : Real.sqrt a > 0 := by positivity
        have h17 : Real.sqrt a ^ 2 = a := by
          rw [Real.sq_sqrt]
          positivity
        have h78 : (1 + 1 / Real.sqrt a : ℝ) / ((1 + 1 / Real.sqrt a) - 1) = Real.sqrt a + 1 := by
          field_simp [Real.sqrt_pos.mpr (show 0 < a by linarith)]
          all_goals nlinarith [Real.sqrt_nonneg a, Real.sq_sqrt (show (0 : ℝ) ≤ (a : ℝ) by linarith)]
        have h45 : a * (1 + 1 / Real.sqrt a) = a + Real.sqrt a := by
          have h76 : Real.sqrt a > 0 := by positivity
          field_simp
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (a : ℝ) by linarith)]
        nlinarith [Real.sqrt_nonneg a, Real.sq_sqrt (show (0 : ℝ) ≤ (a : ℝ) by linarith)]
      nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sq_sqrt (show (0 : ℝ) ≤ (a : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (b : ℝ) by linarith)]
    have h2 : √a + 1 > √b := by
      have h177 : (√a + 1) ^ 2 > (√b) ^ 2 := by
        have h1' : (√a + 1) ^ 2 > b := h1
        have h3 : (√b) ^ 2 = b := Real.sq_sqrt (show (0 : ℝ) ≤ (b : ℝ) by linarith)
        nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, h1', h3]
      have h4 : (√a + 1) ^ 2 ≥ 0 := by positivity
      have h5 : (√b) ^ 2 ≥ 0 := by positivity
      have h10 : (√a + 1) ^ 2 > (√b) ^ 2 := h177
      have h11 : (√a + 1 : ℝ) ≥ 0 := by nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
      have h12 : (√b : ℝ) ≥ 0 := Real.sqrt_nonneg b
      nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, sq_nonneg (√a + 1 - √b), sq_nonneg (√a + 1 + √b)]
    exact h2