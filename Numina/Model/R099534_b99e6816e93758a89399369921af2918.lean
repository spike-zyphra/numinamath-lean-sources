import Mathlib

theorem algebra_326026 (a : ℤ) (h : ∃ x : ℝ, x^2 / (x^2 + 1) - 4 * |x| / Real.sqrt (x^2 + 1) = a - 3) :
    a = 1 ∨ a = 2 ∨ a = 3 := by
  rcases h with ⟨x, hx⟩
  have h1 : x^2 / (x^2 + 1) = ( (|x| / Real.sqrt (x^2 + 1)) ) ^ 2 := by
    field_simp
    <;> ring_nf <;> simp [Real.sqrt_sq]
    <;> ring
  have h2 : x^2 / (x^2 + 1) - 4 * |x| / Real.sqrt (x^2 + 1) = ((|x| / Real.sqrt (x^2 + 1)) ^ 2 - 4 * (|x| / Real.sqrt (x^2 + 1)) ) := by
    rw [h1]
    <;> ring
  have eq1 : ((|x| / Real.sqrt (x^2 + 1)) ^ 2 - 4 * (|x| / Real.sqrt (x^2 + 1)) ) = (a - 3 : ℝ) := by 
    linarith [hx, h2]
  have h3 : (|x| / Real.sqrt (x^2 + 1) ) ≥ (0 : ℝ) := by 
    apply div_nonneg
    · -- Show that |x| ≥ 0
      exact abs_nonneg x
    · -- Show that sqrt(x^2 + 1) ≥ 0
      positivity
  have h4 : (|x| / Real.sqrt (x^2 + 1) ) < (1 : ℝ) := by
    have h5 : |x| < Real.sqrt (x^2 + 1) := by
      have h6 : (|x|) ^ 2 < (Real.sqrt (x^2 + 1)) ^ 2 := by
        have h7 : (|x|) ^ 2 = x^2 := by 
          rw [sq_abs]
        have h8 : (Real.sqrt (x^2 + 1)) ^ 2 = x^2 + 1 := Real.sq_sqrt (by positivity)
        rw [h7, h8]
        linarith
      have h9 : Real.sqrt (x^2 + 1) ≥ 0 := by positivity
      nlinarith [Real.sqrt_nonneg (x^2 + 1), abs_nonneg x, Real.sq_sqrt (show (0 : ℝ) ≤ x^2 + 1 by positivity)]
    have h6 : (|x| / Real.sqrt (x^2 + 1) ) < (1 : ℝ) := by
      apply (div_lt_iff₀ (by positivity)).mpr
      linarith [h5]
    linarith
  have h6 : (a : ℝ) > (0 : ℝ) := by 
    nlinarith [sq_nonneg ( (|x| / Real.sqrt (x^2 + 1) ) - 2 + Real.sqrt (1 + (a : ℝ) ) ), 
      sq_nonneg ( (|x| / Real.sqrt (x^2 + 1) ) - 2 - Real.sqrt (1 + (a : ℝ)  )  ), 
      Real.sqrt_nonneg (1 + (a : ℝ) ), Real.sq_sqrt (show (0 : ℝ) ≤ (1 + (a : ℝ) )  by 
        have ha1 : (a : ℝ) + 1 ≥ (0 : ℝ)  :=  by nlinarith
        linarith ), 
      eq1, h3, h4 ]
  have h7 : (a : ℝ) ≤ (3 : ℝ)  :=  by
    nlinarith [sq_nonneg ( (|x| / Real.sqrt (x^2 + 1) ) - 2 + Real.sqrt (1 + (a : ℝ)  )  ), 
      sq_nonneg ( (|x| / Real.sqrt (x^2 + 1) ) - 2 - Real.sqrt (1 + (a : ℝ)  )  ), 
      Real.sqrt_nonneg (1 + (a : ℝ)  ), Real.sq_sqrt (show (0 : ℝ) ≤ (1 + (a : ℝ)  )  by 
        have ha1 : (a : ℝ) + 1 ≥ (0 : ℝ)  :=  by nlinarith
        linarith  ), 
      eq1, h3, h4  ]
  have ha1 : a > 0  :=  by
    by_contra h
    push_neg at h
    have h2 : (a : ℝ) ≤ (0 : ℝ)  :=  by exact_mod_cast h
    linarith 
  have ha2  :  a ≤ 3  :=  by
    by_contra h
    push_neg at h
    have h3  :  (a : ℝ) > (3 : ℝ)  :=  by exact_mod_cast h 
    linarith 
  have ha3 : a = 1 ∨ a = 2 ∨ a = 3 := by 
    omega 
  exact ha3