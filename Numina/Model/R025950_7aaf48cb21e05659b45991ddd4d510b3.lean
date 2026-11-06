import Mathlib

open Real Set

theorem algebra_309747 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (f : ℝ → ℝ) (hf : f = fun x => sqrt (x ^ 2 + a) + sqrt ((c - x) ^ 2 + b)) :
    IsLeast (range f) (sqrt (c ^ 2 + (sqrt a + sqrt b) ^ 2)) := by

  have h1 : ∀ x, f x = sqrt (x ^ 2 + a) + sqrt ((c - x) ^ 2 + b) := by
    intro x
    rw [hf]

  have h2 : sqrt (c ^ 2 + (sqrt a + sqrt b) ^ 2) ∈ range f := by
    use (sqrt a * c / (sqrt a + sqrt b))
    rw [h1]
    have h3 : 0 < sqrt a := Real.sqrt_pos.mpr ha
    have h4 : 0 < sqrt b := Real.sqrt_pos.mpr hb
    have h5 : sqrt a + sqrt b > 0 := by positivity
    have eq1 : sqrt ( (sqrt a * c / (sqrt a + sqrt b)) ^ 2 + a ) + sqrt ( (c - (sqrt a * c / (sqrt a + sqrt b)) ) ^ 2 + b ) = sqrt (c ^ 2 + (sqrt a + sqrt b) ^ 2) := by
      have h8 : sqrt ( (sqrt a * c / (sqrt a + sqrt b) ) ^ 2 + a ) = sqrt a / (sqrt a + sqrt b) * sqrt (c ^ 2 + (sqrt a + sqrt b) ^ 2) := by
        have h9 : (sqrt a / (sqrt a + sqrt b)) ^ 2 * (c ^ 2 + (sqrt a + sqrt b) ^ 2) = (sqrt a * c / (sqrt a + sqrt b)) ^ 2 + a := by
          field_simp
          ring_nf
          <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ a by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ b by linarith), mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]
        have h10 : sqrt ( (sqrt a * c / (sqrt a + sqrt b) ) ^ 2 + a ) = sqrt ( (sqrt a / (sqrt a + sqrt b) ) ^ 2 * (c ^ 2 + (sqrt a + sqrt b) ^ 2) ) := by 
          rw [h9]
        have h11 : sqrt ( (sqrt a / (sqrt a + sqrt b) ) ^ 2 * (c ^ 2 + (sqrt a + sqrt b) ^ 2) ) = sqrt ( (sqrt a / (sqrt a + sqrt b) ) ^ 2 ) * sqrt (c ^ 2 + (sqrt a + sqrt b) ^ 2) := by
          rw [Real.sqrt_mul (by positivity)]
        have h12 : sqrt ( (sqrt a / (sqrt a + sqrt b) ) ^ 2 ) = sqrt a / (sqrt a + sqrt b) := by
          rw [Real.sqrt_sq (by
            have h_pos1 : sqrt a > 0 := by positivity
            have h_pos2 : sqrt a + sqrt b > 0 := by positivity
            have h_pos3 : sqrt a / (sqrt a + sqrt b) > 0 := by positivity
            linarith
          )]
        rw [h10, h11, h12]
      have h10 : sqrt ( (c - (sqrt a * c / (sqrt a + sqrt b))) ^ 2 + b ) = sqrt b / (sqrt a + sqrt b) * sqrt (c ^ 2 + (sqrt a + sqrt b) ^ 2) := by
        have h11 : (sqrt b / (sqrt a + sqrt b) ) ^ 2 * (c ^ 2 + (sqrt a + sqrt b) ^ 2) = (c - (sqrt a * c / (sqrt a + sqrt b))) ^ 2 + b := by
          field_simp
          ring_nf
          <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ a by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ b by linarith), mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]
        have h12 : sqrt ( (c - (sqrt a * c / (sqrt a + sqrt b)) ) ^ 2 + b ) = sqrt ( (sqrt b / (sqrt a + sqrt b) ) ^ 2 * (c ^ 2 + (sqrt a + sqrt b) ^ 2) ) := by 
          rw [h11]
        have h13 : sqrt ( (sqrt b / (sqrt a + sqrt b) ) ^ 2 * (c ^ 2 + (sqrt a + sqrt b) ^ 2) ) = sqrt ( (sqrt b / (sqrt a + sqrt b) ) ^ 2 ) * sqrt (c ^ 2 + (sqrt a + sqrt b) ^ 2) := by 
          rw [Real.sqrt_mul (by positivity)]
        have h14 : sqrt ( (sqrt b / (sqrt a + sqrt b) ) ^ 2 ) = sqrt b / (sqrt a + sqrt b) := by 
          rw [Real.sqrt_sq (by
            have h_pos1 : sqrt b > 0 := by positivity
            have h_pos2 : sqrt a + sqrt b > 0 := by positivity
            have h_pos3 : sqrt b / (sqrt a + sqrt b) > 0 := by positivity
            linarith
          )]
        rw [h12, h13, h14]
      rw [h8, h10]
      field_simp
      <;> nlinarith [Real.sqrt_nonneg (c ^ 2 + (sqrt a + sqrt b) ^ 2), Real.sqrt_nonneg a, Real.sqrt_nonneg b, mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]
    linarith [eq1]

  constructor 
  · exact h2
  · -- Show that it's minimal
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [h1] at hx
    have h6 : sqrt (x ^ 2 + a) + sqrt ((c - x) ^ 2 + b) ≥ sqrt (c ^ 2 + (sqrt a + sqrt b) ^ 2) := by
      have h7 : (sqrt (x ^ 2 + a) + sqrt ((c - x) ^ 2 + b)) ^ 2 ≥ (sqrt (c ^ 2 + (sqrt a + sqrt b) ^ 2)) ^ 2 := by 
        have h8 : sqrt (x ^ 2 + a) ≥ 0 := Real.sqrt_nonneg (x ^ 2 + a)
        have h9 : sqrt ((c - x) ^ 2 + b) ≥ 0 := Real.sqrt_nonneg ((c - x) ^ 2 + b)
        have h10 : sqrt (c ^ 2 + (sqrt a + sqrt b) ^ 2) ≥ 0 := Real.sqrt_nonneg (c ^ 2 + (sqrt a + sqrt b) ^ 2)
        have h111 : (sqrt (x ^ 2 + a) + sqrt ((c - x) ^ 2 + b)) ^ 2 = 
          (sqrt (x ^ 2 + a)) ^ 2 + (sqrt ((c - x) ^ 2 + b)) ^ 2 + 2 * (sqrt (x ^ 2 + a) * sqrt ((c - x) ^ 2 + b)) := by 
          ring
        have h112 : (sqrt (c ^ 2 + (sqrt a + sqrt b) ^ 2)) ^ 2 = c ^ 2 + (sqrt a + sqrt b) ^ 2 := by 
          exact Real.sq_sqrt (by positivity)
        rw [h111, h112]
        have h13 : (sqrt (x ^ 2 + a)) ^ 2 = x ^ 2 + a := Real.sq_sqrt (by positivity)
        have h14 : (sqrt ((c - x) ^ 2 + b)) ^ 2 = (c - x) ^ 2 + b := Real.sq_sqrt (by positivity)
        rw [h13, h14]
        nlinarith [ sq_nonneg (x - c * (sqrt a) / (sqrt a + sqrt b)), sq_nonneg ( (c - x) - c * (sqrt b) / (sqrt a + sqrt b) ), 
          Real.sqrt_nonneg (x ^ 2 + a), Real.sqrt_nonneg ((c - x) ^ 2 + b), 
          mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b), 
          Real.sq_sqrt (show (0 : ℝ) ≤ a by linarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ b by linarith), 
          sq_nonneg (x * Real.sqrt b - (c - x) * Real.sqrt a), 
          Real.sqrt_nonneg (x^2 + a), Real.sqrt_nonneg ((c - x)^2 + b), 
          mul_nonneg (Real.sqrt_nonneg (x ^ 2 + a)) (Real.sqrt_nonneg ((c - x) ^ 2 + b))
        ]
      have h7a : sqrt (x ^ 2 + a) + sqrt ((c - x) ^ 2 + b) ≥ 0 := by positivity
      have h7b : sqrt (c ^ 2 + (sqrt a + sqrt b) ^ 2) ≥ 0 := by positivity
      nlinarith [ Real.sqrt_nonneg (c ^ 2 + (sqrt a + sqrt b) ^ 2), Real.sqrt_nonneg (x ^ 2 + a), Real.sqrt_nonneg ((c - x) ^ 2 + b), Real.sq_sqrt (show 0 ≤ c ^ 2 + (sqrt a + sqrt b) ^ 2 by positivity), Real.sq_sqrt (show 0 ≤ (x ^ 2 + a : ℝ) by positivity), Real.sq_sqrt (show 0 ≤ ( (c - x) ^ 2 + b : ℝ) by positivity)
      ]
    linarith [h6, hx]