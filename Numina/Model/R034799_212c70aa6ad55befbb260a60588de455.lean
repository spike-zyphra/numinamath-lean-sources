import Mathlib

open Real

theorem inequalities_57231 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b * c = 1) :
    3 ≤ (sqrt a + sqrt b + sqrt c) / 2 + 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) := by 
  have h21 : ∀ x : ℝ, 0 < x → 1 / (1 + x) ≥ (2 - Real.sqrt x) / 2 := by
    intro x hx
    have h1 : 0 < (1 + x : ℝ) := by nlinarith
    have h20 : Real.sqrt x ≥ 0 := by positivity
    have h21 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (show 0 ≤ x by linarith)
    have h40 : (1 / (1 + x) : ℝ) ≥ (2 - Real.sqrt x) / 2 := by
      have h17 : (1 / (1 + x) - (2 - Real.sqrt x) / 2) ≥ 0 := by
        have h13 : (1 / (1 + x) - (2 - Real.sqrt x) / 2) = ( (2 - (2 - Real.sqrt x) * (1 + x)) ) / (2 * (1 + x)) := by
          field_simp
          <;> ring
        rw [h13] 
        apply div_nonneg
        · -- Show numerator is non-negative
          nlinarith [ sq_nonneg (Real.sqrt x - 1) , Real.sqrt_nonneg x, sq_nonneg (x - 1), sq_nonneg (Real.sqrt x ^ 2 - x) ]
        all_goals positivity
      nlinarith
    assumption
  have h23 : 1 / (1 + a) ≥ (2 - Real.sqrt a) / 2 := by
    apply h21 a
    all_goals nlinarith
  have h24 : 1 / (1 + b) ≥ (2 - Real.sqrt b) / 2 := by
    apply h21 b
    all_goals nlinarith
  have h25 : 1 / (1 + c) ≥ (2 - Real.sqrt c) / 2 := by
    apply h21 c
    all_goals nlinarith
  have h40 : (sqrt a + sqrt b + sqrt c) / 2 + 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) ≥ 3 := by
    have h27 : (sqrt a + sqrt b + sqrt c) / 2 + 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) ≥ (sqrt a + sqrt b + sqrt c) / 2 + (2 - sqrt a) / 2 + (2 - sqrt b) / 2 + (2 - sqrt c) / 2 := by
      have h10 : 1 / (1 + a) ≥ (2 - sqrt a) / 2 := h23
      have h11 : 1 / (1 + b) ≥ (2 - sqrt b) / 2 := h24
      have h12 : 1 / (1 + c) ≥ (2 - sqrt c) / 2 := h25
      linarith
    have h30 : (sqrt a + sqrt b + sqrt c) / 2 + (2 - sqrt a) / 2 + (2 - sqrt b) / 2 + (2 - sqrt c) / 2 = 3 := by 
      nlinarith
    linarith
  linarith