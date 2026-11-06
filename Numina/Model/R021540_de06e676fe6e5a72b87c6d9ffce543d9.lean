import Mathlib

open Real Set
open scoped BigOperators

/- The range of the function $f\left( x \right)=2\left| \sin x \right|+3\left| \cos x \right|$ is ___          ___. -/
theorem algebra_11684 : range (λ x => 2 * abs (sin x) + 3 * abs (cos x)) = {y | 2 ≤ y ∧ y ≤ sqrt 13} := by 
  ext y 
  simp only [mem_range, mem_setOf_eq]
  constructor 
  · -- First, we show that if y ∈ range f, then 2 ≤ y ≤ √13
    intro h 
    rcases h with ⟨x, hx⟩
    have h2 : 2 * abs (sin x) + 3 * abs (cos x) ≥ 2 := by 
      cases' abs_cases (sin x) with hsin hsin <;> cases' abs_cases (cos x) with hcos hcos <;> 
        try { 
          nlinarith [Real.sin_sq_add_cos_sq x, sq_nonneg (sin x - 0), sq_nonneg (cos x - 0), sq_nonneg (sin x), sq_nonneg (cos x), Real.sin_sq_add_cos_sq x]
        }
    have h4 : (2 * abs (sin x) + 3 * abs (cos x)) ^ 2 ≤ 13 := by
      have h5 : (2 * abs (sin x) + 3 * abs (cos x)) ^ 2 =
          4 * (abs (sin x) )^2 + 9 * (abs (cos x))^2 + 12 * (abs (sin x) ) * (abs (cos x)) := by
        ring 
      rw [h5]
      have h6 : (abs (sin x) )^2 + (abs (cos x))^2 = 1 := by
        have hsin : (abs (sin x) )^2 = (sin x) ^2 := by 
          simp [abs_pow]
        have hcos : (abs (cos x) )^2 = (cos x) ^2 := by 
          simp [abs_pow]
        have h1 : (sin x) ^2 + (cos x) ^2 = 1 := Real.sin_sq_add_cos_sq x
        linarith [hsin, hcos, h1]
      have h7 : 4 * (abs (sin x) )^2 + 9 * (abs (cos x))^2 + 12 * (abs (sin x) ) * (abs (cos x)) ≤ 13 := by 
        nlinarith [sq_nonneg ((abs (sin x) ) * 3 - (abs (cos x) ) * 2), sq_nonneg ((abs (sin x) ) - 0), sq_nonneg ((abs (cos x) ) - 0), 
                  Real.sin_sq_add_cos_sq x, abs_nonneg (sin x), abs_nonneg (cos x),
                  mul_nonneg (abs_nonneg (sin x)) (abs_nonneg (cos x)), 
                  sq_nonneg (abs (sin x) ), sq_nonneg (abs (cos x) ), h6]
      linarith
    have h3 : (2 * abs (sin x) + 3 * abs (cos x)) ≤ Real.sqrt 13 := by 
      have h4' : (2 * abs (sin x) + 3 * abs (cos x)) ^ 2 ≤ 13 := h4
      have h5 : (2 * abs (sin x) + 3 * abs (cos x)) ≤ Real.sqrt 13 := by
        have h6 : Real.sqrt ((2 * abs (sin x) + 3 * abs (cos x)) ^ 2) ≤ Real.sqrt (13) := by
          apply Real.sqrt_le_sqrt 
          linarith
        have h7 : Real.sqrt ((2 * abs (sin x) + 3 * abs (cos x)) ^ 2) = (2 * abs (sin x) + 3 * abs (cos x)) := by 
          rw [Real.sqrt_sq (show 0 ≤ 2 * abs (sin x) + 3 * abs (cos x) by 
              cases' abs_cases (sin x) with h1 h1 <;> cases' abs_cases (cos x) with h2 h2 <;> linarith
            )
          ]
        nlinarith [h7, h6]
      linarith
    constructor 
    · -- Show 2 ≤ y 
      linarith [h2, hx] 
    · -- Show y ≤ Real.sqrt 13
      linarith [h3, hx]
  · -- Now, we prove the reverse: if y ∈ [2, Real.sqrt 13], then y is in the range
    rintro ⟨hy1, hy2⟩ 
    have h8 : 0 ≤ 13 - y^2 := by
      have h9 : y^2 ≤ 13 := by
        have h10 : y ≤ Real.sqrt 13 := hy2
        have h11 : y ≥ -Real.sqrt 13 := by nlinarith [show Real.sqrt 13 ≥ 0 by positivity, hy1, hy2]
        have h12 : y^2 ≤ (Real.sqrt 13) ^2 := by nlinarith [h10, h11, Real.sqrt_nonneg 13]
        have h13 : (Real.sqrt 13) ^2 = 13 := Real.sq_sqrt (show 0 ≤ (13 : ℝ) by norm_num)
        nlinarith [h13]
      linarith
    use (Real.arcsin ((2 * y + 3 * Real.sqrt (13 - y ^ 2)) / 13))
    have h11 : sin (Real.arcsin ((2 * y + 3 * Real.sqrt (13 - y ^ 2)) / 13)) = (2 * y + 3 * Real.sqrt (13 - y ^ 2)) / 13 := by 
      apply Real.sin_arcsin 
      · -- Show that -1 ≤ (2 * y + 3 * Real.sqrt (13 - y ^ 2)) / 13 
        nlinarith [Real.sqrt_nonneg (13 - y ^ 2), 
          sq_nonneg (y - 2), 
          sq_nonneg (Real.sqrt (13 - y ^ 2) ), 
          Real.sq_sqrt (show 0 ≤ (13 - y ^ 2 : ℝ) by linarith [h8] ), 
          sq_nonneg (y ^ 2 - 4), 
          mul_nonneg (Real.sqrt_nonneg (13 - y ^ 2)) (Real.sqrt_nonneg (13 - y ^ 2)), 
          Real.sqrt_nonneg (13 - y ^ 2)
        ]
      · -- Show that (2 * y + 3 * Real.sqrt (13 - y ^ 2)) / 13 ≤ 1 
        nlinarith [Real.sqrt_nonneg (13 - y ^ 2), 
          sq_nonneg (y - 2), 
          sq_nonneg (Real.sqrt (13 - y ^ 2) ), 
          Real.sq_sqrt (show 0 ≤ (13 - y ^ 2 : ℝ) by linarith [h8] ), 
          sq_nonneg (y ^ 2 - 4), 
          mul_nonneg (Real.sqrt_nonneg (13 - y ^ 2)) (Real.sqrt_nonneg (13 - y ^ 2)), 
          Real.sqrt_nonneg (13 - y ^ 2)
        ]
    have h12 : cos (Real.arcsin ((2 * y + 3 * Real.sqrt (13 - y ^ 2)) / 13)) = Real.sqrt (1 - ((2 * y + 3 * Real.sqrt (13 - y ^ 2)) / 13) ^ 2) := by 
      rw [Real.cos_arcsin]
    have h13 : Real.sqrt (1 - ((2 * y + 3 * Real.sqrt (13 - y ^ 2)) / 13) ^ 2) = (3 * y - 2 * Real.sqrt (13 - y ^ 2)) / 13 := by 
      rw [Real.sqrt_eq_iff_sq_eq] <;> 
        nlinarith [Real.sqrt_nonneg (13 - y ^ 2), 
          sq_nonneg (y - 2), 
          sq_nonneg (Real.sqrt (13 - y ^ 2) ), 
          Real.sq_sqrt (show 0 ≤ (13 - y ^ 2 : ℝ) by linarith [h8] ), 
          sq_nonneg (y ^ 2 - 4), 
          mul_nonneg (Real.sqrt_nonneg (13 - y ^ 2)) (Real.sqrt_nonneg (13 - y ^ 2)), 
          Real.sqrt_nonneg (13 - y ^ 2)
        ]
    have h14 : sin (Real.arcsin ((2 * y + 3 * Real.sqrt (13 - y ^ 2)) / 13)) ≥ 0 := by 
      linarith [h11, show (2 * y + 3 * Real.sqrt (13 - y ^ 2)) / 13 ≥ 0 by
        nlinarith [Real.sqrt_nonneg (13 - y ^ 2), 
          sq_nonneg (y - 2), 
          sq_nonneg (Real.sqrt (13 - y ^ 2) ), 
          Real.sq_sqrt (show 0 ≤ (13 - y ^ 2 : ℝ) by linarith [h8] ), 
          sq_nonneg (y ^ 2 - 4), 
          mul_nonneg (Real.sqrt_nonneg (13 - y ^ 2)) (Real.sqrt_nonneg (13 - y ^ 2)), 
          Real.sqrt_nonneg (13 - y ^ 2)
        ]
      ]
    have h15 : cos (Real.arcsin ((2 * y + 3 * Real.sqrt (13 - y ^ 2)) / 13)) ≥ 0 := by 
      rw [h12, h13]
      nlinarith [Real.sqrt_nonneg (13 - y ^ 2), 
        sq_nonneg (y - 2), 
        sq_nonneg (Real.sqrt (13 - y ^ 2) ), 
        Real.sq_sqrt (show 0 ≤ (13 - y ^ 2 : ℝ) by linarith [h8] ), 
        sq_nonneg (y ^ 2 - 4), 
        mul_nonneg (Real.sqrt_nonneg (13 - y ^ 2)) (Real.sqrt_nonneg (13 - y ^ 2)), 
        Real.sqrt_nonneg (13 - y ^ 2)
      ]
    have h10 : 2 * abs (sin (Real.arcsin ((2 * y + 3 * Real.sqrt (13 - y ^ 2)) / 13)) ) + 3 * abs (cos (Real.arcsin ((2 * y + 3 * Real.sqrt (13 - y ^ 2)) / 13)) ) = y := by 
      have h21 : abs (sin (Real.arcsin ((2 * y + 3 * Real.sqrt (13 - y ^ 2)) / 13)) ) = sin (Real.arcsin ((2 * y + 3 * Real.sqrt (13 - y ^ 2)) / 13)) := by 
        rw [abs_of_nonneg h14]
      have h22 : abs (cos (Real.arcsin ((2 * y + 3 * Real.sqrt (13 - y ^ 2)) / 13)) ) = cos (Real.arcsin ((2 * y + 3 * Real.sqrt (13 - y ^ 2)) / 13)) := by 
        rw [abs_of_nonneg h15]
      rw [h21, h22]
      rw [h11, h12, h13]
      nlinarith [Real.sqrt_nonneg (13 - y ^ 2), 
        sq_nonneg (y - 2), 
        sq_nonneg (Real.sqrt (13 - y ^ 2) ), 
        Real.sq_sqrt (show 0 ≤ (13 - y ^ 2 : ℝ) by linarith [h8] ), 
        sq_nonneg (y ^ 2 - 4), 
        mul_nonneg (Real.sqrt_nonneg (13 - y ^ 2)) (Real.sqrt_nonneg (13 - y ^ 2)), 
        Real.sqrt_nonneg (13 - y ^ 2)
      ]
    linarith [h10]