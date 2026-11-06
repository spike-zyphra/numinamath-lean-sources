import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_106977 :
  {x : ℤ | 0 ≤ x ∧ x ≤ 2012 ∧
    1 / (sqrt x + sqrt 1006) + 1 / (sqrt (2012 - x) + sqrt 1006) =
    2 / (sqrt x + sqrt (2012 - x))}.ncard = 2013 := by
  have h1 : {x : ℤ | 0 ≤ x ∧ x ≤ 2012 ∧
      1 / (sqrt x + sqrt 1006) + 1 / (sqrt (2012 - x) + sqrt 1006) =
      2 / (sqrt x + sqrt (2012 - x))
  } = Set.Icc (0 : ℤ) 2012 := by
    ext x 
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · -- First, prove the forward direction: if x in the set, then in the interval
      rintro ⟨hx1, hx2, heq⟩
      exact ⟨hx1, hx2⟩
    · -- Now prove the reverse direction: if x in the interval, then in the set
      intro h
      rcases h with ⟨hx1, hx2⟩
      constructor
      · exact hx1
      constructor
      · exact hx2
      · -- Now we verify the equation.
        have h1 : (x : ℝ) ≥ 0 := by exact_mod_cast hx1
        have h2 : (x : ℝ) ≤ (2012 : ℝ) := by exact_mod_cast hx2
        have h10 : sqrt (x : ℝ) ≥ 0 := Real.sqrt_nonneg (x : ℝ)
        have h20 : sqrt (2012 - (x : ℝ)) ≥ 0 := Real.sqrt_nonneg (2012 - (x : ℝ))
        have h50 : sqrt (x : ℝ) ^ 2 = (x : ℝ) := by 
          rw [Real.sq_sqrt]
          linarith
        have h60 : sqrt (2012 - (x : ℝ)) ^ 2 = (2012 - (x : ℝ)) := by 
          rw [Real.sq_sqrt]
          linarith
        -- Prove sqrt (x + sqrt (2012 - x)) > 0
        have hx8 : sqrt (x : ℝ) + sqrt (2012 - (x : ℝ)) > 0 := by
          by_contra h
          push_neg at h
          have h11 : sqrt (x : ℝ) = 0 := by
            nlinarith [show sqrt (x : ℝ) ≥ 0 by positivity, 
              show sqrt (2012 - (x : ℝ)) ≥ 0 by positivity, h]
          have h12 : sqrt (2012 - (x : ℝ)) = 0 := by 
            nlinarith [show sqrt (x : ℝ) ≥ 0 by positivity, 
              show sqrt (2012 - (x : ℝ)) ≥ 0 by positivity, h]
          have h13 : (x : ℝ) = 0 := by 
            rw [Real.sqrt_eq_zero (by linarith)] at h11 
            linarith
          have h14 : (2012 - (x : ℝ)) = 0 := by
            rw [Real.sqrt_eq_zero (by linarith)] at h12 
            linarith 
          nlinarith 
        -- Prove sqrt (x + sqrt 1006) ≠ 0
        have h70 : sqrt (x : ℝ) + sqrt (1006 : ℝ) ≠ 0 := by
          have h11 : sqrt (x : ℝ) ≥ 0 := Real.sqrt_nonneg (x : ℝ)
          have h13 : sqrt (1006 : ℝ) > 0 := by positivity
          by_contra h
          have h14 : sqrt (x : ℝ) + sqrt (1006 : ℝ) = 0 := by linarith
          nlinarith [show sqrt (x : ℝ) ≥ 0 by positivity, 
            show sqrt (1006 : ℝ) > 0 by positivity
          ]
        -- Prove sqrt (2012 - x) + sqrt 1006) ≠ 0
        have h80 : sqrt (2012 - (x : ℝ)) + sqrt (1006 : ℝ) ≠ 0 := by
          have h12 : sqrt (2012 - (x : ℝ)) ≥ 0 := Real.sqrt_nonneg (2012 - (x : ℝ))
          have h13 : sqrt (1006 : ℝ) > 0 := by positivity
          by_contra h
          have h14 : sqrt (2012 - (x : ℝ)) + sqrt (1006 : ℝ) = 0 := by linarith
          nlinarith [show sqrt (2012 - (x : ℝ)) ≥ 0 by positivity, 
            show sqrt (1006 : ℝ) > 0 by positivity
          ]
        -- Prove the equation
        have eq8 : 1 / (sqrt (x : ℝ) + sqrt (1006 : ℝ)) + 1 / (sqrt (2012 - (x : ℝ)) + sqrt (1006 : ℝ)) = 2 / (sqrt (x : ℝ) + sqrt (2012 - (x : ℝ)) ) := by
          have h12 : sqrt (x : ℝ) + sqrt (1006 : ℝ) ≠ 0 := h70
          have h13 : sqrt (2012 - (x : ℝ)) + sqrt (1006 : ℝ) ≠ 0 := h80
          have h14 : sqrt (x : ℝ) + sqrt (2012 - (x : ℝ)) ≠ 0 := by 
            linarith
          field_simp [h12, h13, h14]
          <;> nlinarith [Real.sqrt_nonneg (x : ℝ), 
            Real.sqrt_nonneg (2012 - (x : ℝ)), 
            Real.sqrt_nonneg (1006 : ℝ), 
            sq_nonneg (sqrt (x : ℝ) - sqrt (2012 - (x : ℝ))), 
            sq_nonneg (sqrt (x : ℝ) - sqrt (1006 : ℝ)), 
            sq_nonneg (sqrt (2012 - (x : ℝ)) - sqrt (1006 : ℝ)), 
            h50, h60, Real.sq_sqrt (show (0 : ℝ) ≤ (1006 : ℝ) by norm_num)
          ]
        exact_mod_cast eq8
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp
  <;> native_decide