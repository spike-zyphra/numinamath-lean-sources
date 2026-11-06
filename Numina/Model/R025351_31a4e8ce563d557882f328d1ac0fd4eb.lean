import Mathlib

open Real Set
open scoped Real

theorem inequalities_598242 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a * cos α ^ 2 + b * sin α ^ 2 < c) :
  sqrt a * cos α ^ 2 + sqrt b * sin α ^ 2 < sqrt c := by 
  have h1 : cos α ^ 2 + sin α ^ 2 = 1 := by 
    exact Real.cos_sq_add_sin_sq α
  have h2 : (sqrt a * cos α ^ 2 + sqrt b * sin α ^ 2) ^ 2 ≤ a * cos α ^ 2 + b * sin α ^ 2 := by
    have h3 : 0 ≤ cos α ^ 2 := by 
      nlinarith [sq_nonneg (cos α)]
    have h4 : 0 ≤ sin α ^ 2 := by 
      nlinarith [sq_nonneg (sin α), Real.sin_sq_add_cos_sq α]
    have h5 : cos α ^ 2 + sin α ^ 2 = 1 := by 
      linarith [Real.cos_sq_add_sin_sq α]
    have h6 : (sqrt a * cos α ^ 2 + sqrt b * sin α ^ 2) ^ 2 =
        a * cos α ^ 4 + b * sin α ^ 4 + 2 * (sqrt a * sqrt b) * (cos α ^ 2 * sin α ^ 2) := by
      calc
        (sqrt a * cos α ^ 2 + sqrt b * sin α ^ 2) ^ 2 
          = (sqrt a * cos α ^ 2) ^ 2 + (sqrt b * sin α ^ 2) ^ 2 + 2 * (sqrt a * cos α ^ 2 * (sqrt b * sin α ^ 2)) := by ring
        _ = a * (cos α ^ 2) ^ 2 + b * (sin α ^ 2) ^ 2 + 2 * (sqrt a * sqrt b) * (cos α ^ 2 * sin α ^ 2) := by 
          have h61 : (sqrt a * cos α ^ 2) ^ 2 = a * (cos α ^ 2) ^ 2 := by
            calc
              (sqrt a * cos α ^ 2) ^ 2 = (sqrt a) ^ 2 * (cos α ^ 2) ^ 2 := by ring
              _ = a * (cos α ^ 2) ^ 2 := by rw [Real.sq_sqrt]; all_goals linarith
          have h62 : (sqrt b * sin α ^ 2) ^ 2 = b * (sin α ^ 2) ^ 2 := by
            calc
              (sqrt b * sin α ^ 2) ^ 2 = (sqrt b) ^ 2 * (sin α ^ 2) ^ 2 := by ring
              _ = b * (sin α ^ 2) ^ 2 := by rw [Real.sq_sqrt]; all_goals linarith
          rw [h61, h62]
          <;> ring_nf
        _ = a * cos α ^ 4 + b * sin α ^ 4 + 2 * (sqrt a * sqrt b) * (cos α ^ 2 * sin α ^ 2) := by 
          ring_nf
    have h8 : 0 ≤ cos α ^ 2 := by nlinarith [sq_nonneg (cos α)]
    have h9 : 0 ≤ sin α ^ 2 := by nlinarith [sq_nonneg (sin α), Real.sin_sq_add_cos_sq α]
    have h5 : cos α ^ 2 + sin α ^ 2 = 1 := by 
      linarith [Real.cos_sq_add_sin_sq α]
    have h10 : 0 ≤ sqrt a := Real.sqrt_nonneg a
    have h11 : 0 ≤ sqrt b := Real.sqrt_nonneg b
    nlinarith [sq_nonneg (cos α ^ 2 - sin α ^ 2), sq_nonneg (sqrt a - sqrt b), 
      sq_nonneg (sqrt a * cos α ^ 2 - sqrt b * sin α ^ 2), 
      Real.sq_sqrt (show 0 ≤ (a : ℝ) by linarith), 
      Real.sq_sqrt (show 0 ≤ (b : ℝ) by linarith), 
      Real.sqrt_nonneg a, Real.sqrt_nonneg b, 
      mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b), 
      sq_nonneg (cos α ^ 2 * (sqrt a - sqrt b)), 
      sq_nonneg (sin α ^ 2 * (sqrt a - sqrt b)), 
      sq_nonneg (sqrt a ^ 2 - sqrt b ^ 2), 
      mul_nonneg h8 h9
    ]
  -- Now establish the final result.
  have h3 : (sqrt a * cos α ^ 2 + sqrt b * sin α ^ 2) ≥ 0 := by
    positivity
  have h4 : (sqrt a * cos α ^ 2 + sqrt b * sin α ^ 2) ^ 2 < c := by
    linarith [h2, h]
  have h5 : sqrt ((sqrt a * cos α ^ 2 + sqrt b * sin α ^ 2) ^ 2) < sqrt c := by
    apply Real.sqrt_lt_sqrt
    · nlinarith [h3]
    · linarith [h4]
  have h6 : sqrt ((sqrt a * cos α ^ 2 + sqrt b * sin α ^ 2) ^ 2) = sqrt a * cos α ^ 2 + sqrt b * sin α ^ 2 := by
    rw [Real.sqrt_sq (show 0 ≤ sqrt a * cos α ^ 2 + sqrt b * sin α ^ 2 by positivity)]
  linarith [h6, h5]