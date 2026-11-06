import Mathlib

theorem algebra_21564 (n : ℕ) (hn : n = 19941994) : ⌊Real.sqrt (n^2 - 10 * n + 29)⌋ = 19941989 := by 
  rw [hn]
  have h_eq : ((19941994 : ℝ) ^ 2 - 10 * (19941994 : ℝ) + 29) = (19941989 : ℝ) ^ 2 + 4 := by
    norm_num 
  have h1 : Real.sqrt ((19941994 : ℝ) ^ 2 - 10 * (19941994 : ℝ) + 29) = Real.sqrt ((19941989 : ℝ) ^ 2 + 4) := by
    rw [h_eq]
  have h2 : (19941989 : ℝ) < Real.sqrt ((19941989 : ℝ) ^ 2 + 4) := by 
    nlinarith [Real.sqrt_nonneg ((19941989 : ℝ) ^ 2 + 4), Real.sq_sqrt (show (0 : ℝ) ≤ ((19941989 : ℝ) ^ 2 + 4) by positivity)]
  -- Show that the real sqrt is less than the next integer
  have h3 : Real.sqrt ((19941989 : ℝ) ^ 2 + 4) < (19941990 : ℝ) := by 
    nlinarith [Real.sqrt_nonneg ((19941989 : ℝ) ^ 2 + 4), Real.sq_sqrt (show (0 : ℝ) ≤ ((19941989 : ℝ) ^ 2 + 4) by positivity)]
  have h4 : ⌊Real.sqrt ((19941994 : ℝ) ^ 2 - 10 * (19941994 : ℝ) + 29)⌋ = (19941989 : ℤ) := by
    have h5 : Real.sqrt ((19941994 : ℝ) ^ 2 - 10 * (19941994 : ℝ) + 29) = Real.sqrt ((19941989 : ℝ) ^ 2 + 4) := h1
    rw [h5]
    have h5 : ⌊Real.sqrt ((19941989 : ℝ) ^ 2 + 4)⌋ = (19941989 : ℤ) := by 
      rw [Int.floor_eq_iff]
      constructor <;> ( 
        try { 
          have h7 : (19941989 : ℝ) ≤ Real.sqrt ((19941989 : ℝ) ^ 2 + 4) := by 
            nlinarith [Real.sqrt_nonneg ((19941989 : ℝ) ^ 2 + 4), Real.sq_sqrt (show (0 : ℝ) ≤ ((19941989 : ℝ) ^ 2 + 4) by positivity)]
          have h8 : Real.sqrt ((19941989 : ℝ) ^ 2 + 4) < (19941990 : ℝ) := h3
          norm_num at *
          all_goals nlinarith 
        }
      )
    exact_mod_cast h5 
  exact_mod_cast h4