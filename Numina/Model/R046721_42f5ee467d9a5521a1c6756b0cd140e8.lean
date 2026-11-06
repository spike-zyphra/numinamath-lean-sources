import Mathlib

theorem inequalities_175760 : IsGreatest {S : ℝ | ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a * b * c = 1 ∧ S = 1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1)} 1:= by 
  constructor
  · -- Show 1 is in the set.
    use 1, 1, 1
    norm_num
  · -- Show no value greater than 1 belongs to the set
    intro S hS 
    rcases hS with ⟨a, b, c, ha, hb, hc, habc, hS⟩ 
    have h1 : (1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1)) ≤ 1 := by 
      have h3 : 0 < (a + b + 1) * (b + c + 1) * (c + a + 1) := by positivity
      have h5 : 0 < (a + b + 1) := by linarith
      have h6 : 0 < (b + c + 1) := by linarith
      have h7 : 0 < (c + a + 1) := by linarith
      have eq3 : (1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1) ) =  ((b + c + 1) * (c + a + 1) + (a + b + 1) * (c + a + 1) + (a + b + 1) * (b + c + 1)) / ((a + b + 1) * (b + c + 1) * (c + a + 1)) := by 
        field_simp
        ring
      rw [eq3]
      have h10 : ((b + c + 1) * (c + a + 1) + (a + b + 1) * (c + a + 1) + (a + b + 1) * (b + c + 1)) / ((a + b + 1) * (b + c + 1) * (c + a + 1)) ≤ 1 := by
        apply (div_le_iff₀ (by positivity)).mpr 
        -- Now need to show that the numerator ≤ denominator.
        -- Using square ≥ 0, which expands to (a-b)^2 + (b-c)^2 + (c-a)^2 ≥ 0
        -- However, in case of one variable. Depending on variables.
        nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1), 
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
          sq_nonneg (a * b * c - 1), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          habc
        ]
      linarith
    linarith [hS, h1]