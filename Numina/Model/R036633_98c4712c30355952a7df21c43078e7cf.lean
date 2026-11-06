import Mathlib

open Real Set
open scoped Real

theorem inequalities_128154 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a * (cos θ)^2 + b * (sin θ)^2 < c) :
  √a * (cos θ)^2 + √b * (sin θ)^2 < √c := by

  have h1 : (cos θ) ^ 2 + (sin θ) ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  have hc2 : 0 ≤ (cos θ)^2 := by positivity
  have hs2 : 0 ≤ (sin θ)^2 := by positivity

  have h8 : (√a * (cos θ)^2 + √b * (sin θ)^2) ^ 2 < c := by
    have h11 : (√a * (cos θ) ^ 2 + √b * (sin θ) ^ 2) ^ 2 ≤ a * (cos θ) ^ 2 + b * (sin θ) ^ 2 := by
      have h12 : 0 ≤ (cos θ) ^ 2 := by positivity
      have h13 : 0 ≤ (sin θ) ^ 2 := by positivity
      have h14 : (cos θ) ^ 2 + (sin θ) ^ 2 = 1 := h1
      have h15 : (√a * (cos θ) ^ 2 + √b * (sin θ) ^ 2) ^ 2 = 
        a * ((cos θ) ^ 2) ^ 2 + b * ((sin θ) ^ 2) ^ 2 + 2 * (√a * √b) * ((cos θ) ^ 2) * ((sin θ) ^ 2) := by
        have h16 : (√a * (cos θ) ^ 2 + √b * (sin θ) ^ 2) ^ 2 = 
          (√a * (cos θ) ^ 2) ^ 2 + (√b * (sin θ) ^ 2) ^ 2 + 2 * (√a * (cos θ) ^ 2) * (√b * (sin θ) ^ 2) := by ring
        have h17 : (√a * (cos θ) ^ 2) ^ 2 = a * ((cos θ) ^ 2) ^ 2 := by 
          calc 
            (√a * (cos θ) ^ 2) ^ 2 = (√a) ^ 2 * ((cos θ) ^ 2) ^ 2 := by ring 
            _ = a * ((cos θ) ^ 2) ^ 2 := by rw [Real.sq_sqrt (by linarith)]
        have h18 : (√b * (sin θ) ^ 2) ^ 2 = b * ((sin θ) ^ 2) ^ 2 := by 
          calc 
            (√b * (sin θ) ^ 2) ^ 2 = (√b) ^ 2 * ((sin θ) ^ 2) ^ 2 := by ring 
            _ = b * ((sin θ) ^ 2) ^ 2 := by rw [Real.sq_sqrt (by linarith)]
        rw [h16]
        rw [h17, h18]
        <;> ring_nf <;> norm_num
      have h16 : a * ((cos θ) ^ 2) ^ 2 + b * ((sin θ) ^ 2) ^ 2 + 2 * (√a * √b) * ((cos θ) ^ 2) * ((sin θ) ^ 2) ≤ a * (cos θ) ^ 2 + b * (sin θ) ^ 2 := by
        have h17 : (cos θ) ^ 2 * (sin θ) ^ 2 ≥ 0 := by positivity
        have h18 : (√a) ^ 2 = a := Real.sq_sqrt (by linarith)
        have h19 : (√b) ^ 2 = b := Real.sq_sqrt (by linarith)
        have h20 : (√a * √b) ^ 2 = (√a) ^ 2 * (√b) ^ 2 := by ring
        nlinarith [sq_nonneg (√a * (cos θ) ^ 2 - √b * (sin θ) ^ 2), sq_nonneg (√a - √b), 
          Real.sqrt_nonneg a, Real.sqrt_nonneg b, sq_nonneg ((cos θ) ^ 2 - (sin θ) ^ 2), 
          h14, mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
        ]
      linarith [h15, h16]

    have h17 : a * (cos θ) ^ 2 + b * (sin θ) ^ 2 < c := h
    linarith [h11, h17]

  have h9 : √a * (cos θ) ^ 2 + √b * (sin θ) ^ 2 ≥ 0 := by
    positivity

  have h10 : (√c) ^ 2 = c := Real.sq_sqrt (by linarith)

  have h11 : √a * (cos θ)^2 + √b * (sin θ)^2 < √c := by
    by_contra h12
    push_neg at h12
    have h13 : (√a * (cos θ) ^ 2 + √b * (sin θ) ^ 2) ^ 2 ≥ (√c) ^ 2 := by
      have h14 : √a * (cos θ) ^ 2 + √b * (sin θ) ^ 2 ≥ √c := by linarith [h12]
      have h15 : (√a * (cos θ) ^ 2 + √b * (sin θ) ^ 2) ^ 2 ≥ (√c) ^ 2 := by 
        nlinarith [h14, Real.sqrt_nonneg c, Real.sqrt_nonneg a, Real.sqrt_nonneg b, show 0 ≤ √c by positivity]
      linarith [h15]
    nlinarith [h8, h13, Real.sqrt_nonneg c, Real.sqrt_nonneg a, Real.sqrt_nonneg b]

  linarith [h11]