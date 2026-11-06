import Mathlib

open Real

theorem inequalities_28179 (a : ℕ → ℝ) (ha0 : 0 < a 0)
    (han : ∀ n, a (n + 1) = a n / sqrt (1 + 2020 * (a n)^2)) :
    a 2020 < 1 / 2020 := by

  have h1 : ∀ (n : ℕ), (a n) ^ 2 = (a 0) ^ 2 / (1 + (2020 : ℝ) * (a 0) ^ 2 * (n : ℝ)) := by
    intro n
    induction n with
    | zero => 
      norm_num 
    | succ n ih => 
      have eq1 : (a (n + 1) ) ^ 2 = (a n) ^ 2 / (1 + (2020 : ℝ) * (a n) ^ 2) := by 
        rw [han n]
        have h2 : (a n / sqrt (1 + (2020 : ℝ) * (a n) ^ 2) ) ^ 2 = (a n) ^ 2 / (1 + (2020 : ℝ) * (a n) ^ 2) := by
          have h3 : sqrt (1 + (2020 : ℝ) * (a n) ^ 2) > 0 := by 
            apply Real.sqrt_pos.mpr
            positivity
          have h4 : (sqrt (1 + (2020 : ℝ) * (a n) ^ 2)) ^ 2 = 1 + (2020 : ℝ) * (a n) ^ 2 := Real.sq_sqrt (by positivity)
          field_simp [h4]
          <;> nlinarith [Real.sqrt_nonneg (1 + (2020 : ℝ) * (a n) ^ 2), sq_nonneg (a n)]
        linarith [h2] 
      rw [eq1] 
      rw [ih] 
      field_simp
      <;> ring

  have h2 : (a 2020) ^ 2 < (1 / (2020 : ℝ)) ^ 2 := by 
    have h3 : (a 0) ^ 2 > (0 : ℝ) := by 
      nlinarith [ha0] 
    have eq1 : (a 2020) ^ 2 = (a 0) ^ 2 / (1 + (2020 : ℝ) * (a 0) ^ 2 * (2020 : ℝ)) := by
      specialize h1 2020 
      norm_num at h1 ⊢ 
      <;> linarith 
    rw [eq1] 
    have h4 : (a 0) ^ 2 > (0 : ℝ) := h3 
    have h6 : (1 + (2020 : ℝ) * (a 0) ^ 2 * (2020 : ℝ)) > 0 := by 
      nlinarith [h4]
    have h8 : (a 0) ^ 2 < ( (1 / (2020 : ℝ)) ^ 2 ) * (1 + (2020 : ℝ) * (a 0) ^ 2 * (2020 : ℝ) ) := by 
      nlinarith [h4, sq_pos_of_pos h4] 
    have h7 : (a 0) ^ 2 / (1 + (2020 : ℝ) * (a 0) ^ 2 * (2020 : ℝ)) < ( (1 / (2020 : ℝ)) ^ 2 ) := by 
      apply (div_lt_iff₀ (by positivity)).mpr 
      linarith [h8, h4] 
    linarith 
  have h3 : a 2020 ≥ 0 := by
    have h1_pos : ∀ n : ℕ, a n > 0 := by
      intro n
      induction n with
      | zero => 
        exact ha0 
      | succ n ih => 
        have h9 : a (n + 1) = a n / sqrt (1 + 2020 * (a n) ^ 2) := han n 
        rw [h9] 
        apply div_pos 
        exact ih 
        positivity 
    specialize h1_pos 2020 
    linarith

  have h4 : a 2020 < (1 / (2020 : ℝ)) := by 
    have h33 : (a 2020) ≥ 0 := by 
      nlinarith [h3] 
    nlinarith [h2, sq_nonneg (a 2020 - (1 / (2020 : ℝ)) ) ]
  linarith