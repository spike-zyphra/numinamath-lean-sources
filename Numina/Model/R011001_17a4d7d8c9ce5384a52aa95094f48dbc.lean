import Mathlib

theorem inequalities_271062 (p : ℝ) :
    (∀ x y : ℝ, x > 0 → y > 0 → (x ^ 3 + p * y ^ 3) / (x + y) ≥ x * y) ↔ p ≥ 1 := by
  constructor
  · -- Assume inequality holds, prove p >= 1.
    intro h
    specialize h 1 1 (by norm_num) (by norm_num)
    norm_num at h ⊢
    nlinarith
  · -- Assume p >= 1, prove the inequality.
    intro hp x y hx hy
    have h1 : 0 < x + y := by linarith
    have h2 : (x ^ 3 + p * y ^ 3) / (x + y) ≥ x * y := by 
      have h3 : x * y > 0 := mul_pos hx hy
      have h4 : x + y > 0 := h1
      have h5 : (x ^ 3 + p * y ^ 3) ≥ x * y * (x + y) := by
        have h6 : x ^ 3 + 1 * y ^ 3 ≥ x * y * (x + y) := by
          nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), 
            sq_nonneg (x - 2 * y), sq_nonneg (2 * x - y), 
            sq_nonneg (x * y), mul_pos hx hy
          ]
        have h7 : p * y^3 ≥ 1 * y^3 := by
          have h8 : y ^ 3 > 0 := by positivity
          nlinarith [show p ≥ 1 by linarith, show y ^ 3 > 0 by positivity]
        have h8 : x ^ 3 + p * y ^ 3 ≥ x * y * (x + y) := by 
          nlinarith [h6, h7, mul_pos hx (show 0 < y by linarith)]
        linarith
      have h6 : (x ^ 3 + p * y ^ 3) / (x + y) ≥ x * y := by
        apply (le_div_iff₀ (by linarith)).mpr
        nlinarith
      linarith
    linarith [h2]