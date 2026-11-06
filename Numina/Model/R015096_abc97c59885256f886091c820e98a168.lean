import Mathlib

theorem inequalities_598287 (a b c : ℝ) :
    |a + b + c| / (1 + |a + b + c|) ≤
    |a| / (1 + |a|) + |b| / (1 + |b|) + |c| / (1 + |c|) := by
  have h1 : |a + b + c| ≤ |a| + |b| + |c| := by 
    have h2 : |a + b + c| ≤ |a + b| + |c| := by 
      apply abs_add 
    have h12 : |a + b| ≤ |a| + |b| := by 
      apply abs_add 
    have h13 : |a + b| + |c| ≤ |a| + |b| + |c| := by 
      linarith [h12]
    linarith [h2, h13, abs_nonneg (a + b), abs_nonneg c, abs_nonneg a, abs_nonneg b]
  have h11 : abs (a + b + c) / (1 + abs (a + b + c)) ≤ (abs a + abs b + abs c) / (1 + abs a + abs b + abs c) := by 
    have h1' : abs (a + b + c) ≤ abs a + abs b + abs c := h1
    have h13 : abs (a + b + c) ≥ 0 := abs_nonneg (a + b + c)
    have h14 : abs a + abs b + abs c ≥ 0 := by positivity 
    have eq1 : abs (a + b + c) / (1 + abs (a + b + c)) ≤ (abs a + abs b + abs c) / (1 + abs a + abs b + abs c) := by 
      apply (div_le_div_iff (by positivity) (by positivity)).mpr 
      nlinarith [abs_nonneg a, abs_nonneg b, abs_nonneg c, abs_nonneg (a + b + c), 
        mul_nonneg (abs_nonneg a) (abs_nonneg b), 
          mul_nonneg (abs_nonneg a) (abs_nonneg c), 
            mul_nonneg (abs_nonneg b) (abs_nonneg c)]
    assumption 
  have eq1 : |a| / (1 + |a|) + |b| / (1 + |b|) + |c| / (1 + |c|) ≥ (|a| + |b| + |c|) / (1 + |a| + |b| + |c|) := by
    have h41 : |a| ≥ 0 := abs_nonneg a
    have h42 : |b| ≥ 0 := abs_nonneg b
    have h43 : |c| ≥ 0 := abs_nonneg c
    have h44 : 1 + |a| + |b| + |c| > 0 := by linarith 
    have h46 : |a| / (1 + |a|) + |b| / (1 + |b|) + |c| / (1 + |c|) - (|a| + |b| + |c|) / (1 + |a| + |b| + |c|) ≥ 0 := by 
      have h47 : |a| / (1 + |a|) + |b| / (1 + |b|) + |c| / (1 + |c|) - (|a| + |b| + |c|) / (1 + |a| + |b| + |c|) = 
         (|a| * (1 + |a| + |b| + |c|) * (1 + |b|) * (1 + |c|) + 
          |b| * (1 + |a| + |b| + |c|) * (1 + |a|) * (1 + |c|) + 
          |c| * (1 + |a| + |b| + |c|) * (1 + |a|) * (1 + |b|) - 
          (|a| + |b| + |c|) * (1 + |a|) * (1 + |b|) * (1 + |c|)) / 
        ((1 + |a|) * (1 + |b|) * (1 + |c|) * (1 + |a| + |b| + |c|)) := by 
        field_simp
        ring
      rw [h47] at *
      apply div_nonneg 
      · -- Show that the numerator is non-negative
        have h48 : |a| * (1 + |a| + |b| + |c|) * (1 + |b|) * (1 + |c|) + 
            |b| * (1 + |a| + |b| + |c|) * (1 + |a|) * (1 + |c|) + 
            |c| * (1 + |a| + |b| + |c|) * (1 + |a|) * (1 + |b|) - 
            (|a| + |b| + |c|) * (1 + |a|) * (1 + |b|) * (1 + |c|) ≥ 0 := by 
          have h11 : |a| ≥ 0 := abs_nonneg a
          have h12 : |b| ≥ 0 := abs_nonneg b
          have h13 : |c| ≥ 0 := abs_nonneg c 
          nlinarith [sq_nonneg (|a| - |b|), sq_nonneg (|a| - |c|), sq_nonneg (|b| - |c|), 
              sq_nonneg (|a| * |b| - |a| * |c|), sq_nonneg (|a| * |b| - |b| * |c|), sq_nonneg (|a| * |c| - |b| * |c|), 
              mul_nonneg (abs_nonneg a) (abs_nonneg b), 
              mul_nonneg (abs_nonneg a) (abs_nonneg c), 
              mul_nonneg (abs_nonneg b) (abs_nonneg c)]
        linarith 
      positivity 
    linarith 
  have h713 : |a + b + c| / (1 + |a + b + c|) ≤ |a| / (1 + |a|) + |b| / (1 + |b|) + |c| / (1 + |c|) := by 
    linarith [eq1, h11]
  exact h713