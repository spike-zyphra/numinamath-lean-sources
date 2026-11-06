import Mathlib

theorem number_theory_56097 :
    IsLeast {d : ℝ | ∃ a b : ℤ, d = Real.sqrt ((2019 - (21 * a - 19 * b))^2 + (470 - (19 * b + 21 * a))^2)} (Real.sqrt 101) := by 
  constructor 
  · -- Show that sqrt(101) is indeed in the set.
    use 59, -41 
    have h1 : ((2019 - (21 * (59 : ℤ) - 19 * (-41 : ℤ))) : ℝ) ^2 + ((470 - (19 * (-41 : ℤ) + 21 * (59 : ℤ))) : ℝ) ^2 = (101 : ℝ) := by
      norm_num
    have h2 : Real.sqrt ((2019 - (21 * (59 : ℤ) - 19 * (-41 : ℤ)) ) ^ 2 + (470 - (19 * (-41 : ℤ) + 21 * (59 : ℤ)) ) ^ 2) = Real.sqrt 101 := by 
      rw [h1]
    linarith [h2]
  · -- Show that sqrt(101) is the minimum.
    intro d hd
    rcases hd with ⟨a, b, h_eq⟩
    have h1 : (2019 - (21 * a - 19 * b)) ^ 2 + (470 - (19 * b + 21 * a)) ^ 2 ≥ 101 := by 
      by_contra h
      push_neg at h 
      have h2 : (2019 - (21 * a - 19 * b)) ^ 2 + (470 - (19 * b + 21 * a)) ^ 2 < (101 : ℤ) := by 
        omega 
      have h4 : (2019 - (21 * a - 19 * b)) ≤ 10 := by 
        nlinarith [sq_nonneg (2019 - (21 * a - 19 * b) : ℤ), sq_nonneg (470 - (19 * b + 21 * a) : ℤ)]
      have h5 : (2019 - (21 * a - 19 * b)) ≥ -10 := by 
        nlinarith [sq_nonneg (2019 - (21 * a - 19 * b) : ℤ), sq_nonneg (470 - (19 * b + 21 * a) : ℤ)]
      have h6 : (470 - (19 * b + 21 * a)) ≤ 10 := by 
        nlinarith [sq_nonneg (2019 - (21 * a - 19 * b) : ℤ), sq_nonneg (470 - (19 * b + 21 * a) : ℤ)]
      have h7 : (470 - (19 * b + 21 * a)) ≥ -10 := by 
        nlinarith [sq_nonneg (2019 - (21 * a - 19 * b) : ℤ), sq_nonneg (470 - (19 * b + 21 * a) : ℤ)]
      interval_cases h8 : (2019 - (21 * a - 19 * b)) <;> try { 
        omega 
      } <;> try { 
        interval_cases h10 : (470 - (19 * b + 21 * a)) <;> omega 
      }
    have h2 : Real.sqrt ((2019 - (21 * a - 19 * b)) ^2 + (470 - (19 * b + 21 * a)) ^2 ) ≥ Real.sqrt (101 : ℝ) := by 
      have h3 : (2019 - (21 * a - 19 * b)) ^2 + (470 - (19 * b + 21 * a)) ^2 ≥ (101 : ℝ) := by
        exact_mod_cast h1 
      have h4 : Real.sqrt ((2019 - (21 * a - 19 * b)) ^2 + (470 - (19 * b + 21 * a)) ^2 ) ≥ Real.sqrt (101 : ℝ) := by 
        apply Real.sqrt_le_sqrt 
        linarith [h3]
      linarith 
    linarith [h_eq, h2]