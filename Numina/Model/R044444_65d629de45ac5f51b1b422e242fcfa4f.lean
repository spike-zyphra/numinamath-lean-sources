import Mathlib

open Real

theorem algebra_995 {a : ℝ} (ha : 0 < a) (x : ℝ) (hx : x = √(a + √(a + √(a + x)))) (h : x = a) :
    a = 2 := by
  have h1 : a = √(a + √(a + √(a + a))) := by
    rw [show x = a by linarith [h]] at hx
    linarith
  have h3 : a ^ 2 = a + √(a + √(a + a)) := by
    have h3 : a = √(a + √(a + √(a + a))) := h1
    have h4 : a ≥ 0 := by positivity
    have h5 : √(a + √(a + √(a + a))) ≥ 0 := Real.sqrt_nonneg (a + √(a + √(a + a)))
    have h6 : a ^ 2 = a + √(a + √(a + a)) := by
      calc
        a ^ 2 = (√(a + √(a + √(a + a)))) ^ 2 := by rw [show √(a + √(a + √(a + a)) ) = a by linarith [h3] ]
        _ = a + √(a + √(a + a)) := by
          rw [Real.sq_sqrt]
          have h31 : a + √(a + √(a + a)) ≥ 0 := by
            positivity
          linarith [h31]
    linarith
  have h6 : (a ^ 2 - a) ^ 2 = a + √(a + a) := by
    have h61 : a ^ 2 - a = √(a + √(a + a)) := by
      nlinarith [h3]
    have h7 : (a ^ 2 - a) ^ 2 = (√(a + √(a + a)) ) ^ 2 := by
      rw [show √(a + √(a + a)) = a ^ 2 - a by linarith [h61]]
    have h8 : (√(a + √(a + a)) ) ^ 2 = a + √(a + a) := by
      rw [Real.sq_sqrt]
      positivity
    nlinarith [h7, h8]
  -- the equation become $ (a^2 -a)^2 = 2a$.
  have h11 : (a ^ 4 - 2 * a ^ 3 + a ^ 2 - a) ^ 2 = 2 * a := by
    have h10 : (a ^ 2 - a) ^ 2 = a + Real.sqrt (a + a) := h6
    have h14 : (a ^ 2 - a) ^ 2 = a + Real.sqrt (2 * a) := by
      have h12 : Real.sqrt (a + a) = Real.sqrt (2 * a) := by
        have h16 : a + a = 2 * a := by linarith
        rw [h16]
      rw [h12] at h10
      nlinarith [h10]
    have h13 : (a ^ 4 - 2 * a ^ 3 + a ^ 2 - a) = (a ^ 2 - a) ^ 2 - a := by
      nlinarith
    nlinarith [h14, Real.sq_sqrt (show 0 ≤ (2 * a : ℝ) by positivity), Real.sqrt_nonneg (2 * a), sq_nonneg (a ^ 2 - 4 * a + 4), sq_nonneg (a ^ 2 - 2 * a)]
  have h16 : (a - 2) * a = 0 := by
    nlinarith [sq_nonneg (a ^ 2 - a - 2), sq_nonneg (a ^ 2 - 3 * a + 2), sq_nonneg (a * (a - 2)), sq_nonneg ((a - 2) * (a ^ 2)), sq_nonneg (a - 2), sq_nonneg (a ^ 2 - 2), sq_nonneg (a ^ 2 - 2 * a), sq_nonneg (a ^ 2 - 4 * a + 4)]
  have h17 : a - 2 = 0 ∨ a = 0 := by
    cases (mul_eq_zero.mp h16) with
    | inl h22 => 
      left
      linarith
    | inr h22 => 
      right
      nlinarith
  cases h17 with
  | inl h18 =>
    nlinarith
  | inr h19 =>
    nlinarith