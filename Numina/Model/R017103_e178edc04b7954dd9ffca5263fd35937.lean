import Mathlib

open Real Set

theorem algebra_208077 :
    IsLeast {x : ℝ | ∃ s t : ℝ, x = (s + 5 - 3 * abs (cos t))^2 + (s - 2 * abs (sin t))^2} 2 := by
  constructor
  · -- Show that 2 is in the set
    use -1, (0 : ℝ)
    have hcos : abs (cos (0 : ℝ)) = 1 := by
      have h1 : cos (0 : ℝ) = 1 := by 
        simp
      rw [h1]
      norm_num
    have hsin : abs (sin (0 : ℝ)) = 0 := by
      have h1 : sin (0 : ℝ) = 0 := by
        simp
      rw [h1]
      norm_num
    rw [hcos, hsin]
    norm_num
  · -- Show that 2 is the least in the set
    intro x hx
    rcases hx with ⟨s, t, hx⟩
    have h1 : 0 ≤ abs (cos t) := abs_nonneg (cos t)
    have h2 : 0 ≤ abs (sin t) := abs_nonneg (sin t)
    have h3 : abs (cos t) ≤ 1 := by
      apply abs_le.2
      constructor <;> try linarith [Real.cos_le_one t, Real.neg_one_le_cos t]
    have h4 : abs (sin t) ≤ 1 := by
      apply abs_le.2
      constructor <;> try linarith [Real.sin_le_one t, Real.neg_one_le_sin t]
    have h5 : abs (cos t) ^ 2 + abs (sin t) ^ 2 = 1 := by 
      have h11 : abs (cos t) ^ 2 = cos t ^ 2 := by
        simp [abs_pow]
      have h12 : abs (sin t) ^ 2 = sin t ^ 2 := by
        simp [abs_pow]
      have h13 : cos t ^ 2 + sin t ^ 2 = 1 := by 
        exact Real.cos_sq_add_sin_sq t
      nlinarith [h11, h12, h13]
    have h6 : (s + 5 - 3 * abs (cos t)) ^ 2 + (s - 2 * abs (sin t)) ^ 2 ≥ 2 := by
      nlinarith [sq_nonneg (s + 1), sq_nonneg (abs (cos t) - 1), sq_nonneg (abs (sin t) - 0), 
        sq_nonneg ((s + 5 - 3 * abs (cos t)) - (-1 +5 -3 * (abs (cos t)))), sq_nonneg ((s - 2 * abs (sin t)) - (-1 - 0)), 
          abs_nonneg (cos t), abs_nonneg (sin t), 
            mul_nonneg (show 0 ≤ abs (cos t) by apply abs_nonneg) (show 0 ≤ abs (sin t) by apply abs_nonneg), 
              h5
                ]
    linarith [h6, hx]