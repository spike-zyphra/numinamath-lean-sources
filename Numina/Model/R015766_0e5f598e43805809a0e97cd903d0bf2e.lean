import Mathlib

open Real

theorem number_theory_7136 : ¬∃ (x : ℚ), Real.sqrt 26 = x := by
  rintro ⟨x, hx⟩
  have h1 : Real.sqrt 26 ≥ 0 := by positivity
  have h3 : (x : ℝ) ^ 2 = 26 := by
    calc
      (x : ℝ) ^ 2 = (Real.sqrt 26) ^ 2 := by rw [hx]
      _ = 26 := Real.sq_sqrt (by norm_num)
  have h4 : x ^ 2 = (26 : ℚ) := by 
    exact_mod_cast h3
  have h5 : ¬ IsSquare (26 : ℚ) := by
    native_decide
  
  -- We have h4 which is x^2 = 26, so 26 is a square of x ∈ ℚ
  -- But h5 is ¬ IsSquare 26
  -- So contradiction
  -- We construct h6 : IsSquare (26 : ℚ) to have contradiction with h5
  have h6 : IsSquare (26 : ℚ) := by 
    use x
    have h7 : (26 : ℚ) = (x * x : ℚ) := by 
      have hx2 : x ^ 2 = (26 : ℚ) := h4
      have hx_eq : (26 : ℚ) = x ^ 2 := by 
        linarith 
      rw [hx_eq]
      rw [pow_two]
      <;> ring
      all_goals linarith 
    linarith 
  contradiction