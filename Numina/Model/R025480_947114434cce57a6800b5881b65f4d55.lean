import Mathlib

theorem algebra_4731 {A : ℝ} (f : ℝ → ℝ → ℝ) (hf : f = fun x y => 1 / (x * y) + 1 / ((x + 1) * (y + A))) (h : f 2 1 = 2 / 3) :
    f 2017 2018 = 2 / 4072323 := by

  have eq1 : f 2 1 = 1 / (2 * (1 : ℝ)) + 1 / ((2 + 1) * (1 + A)) := by
    rw [hf]

  rw [eq1] at h 

  have eq3 : A = 1 := by
    have eq4' : 1 / (2 * (1 : ℝ)) + 1 / ((2 + 1) * (1 + A)) = 2 / 3 := by 
      linarith 
    have eq5 : 1 / ((2 + 1) * (1 + A)) = 1 / 6 := by
      have eq6 : 1 / ((2 + 1) * (1 + A)) = (2 / (3 : ℝ) - (1 / 2)) := by 
        linarith
      rw [eq6] 
      norm_num
    have eq6 : 3 * (1 + A) = 6 := by 
      have h1 : (2 + 1 : ℝ) * (1 + A) ≠ 0 := by
        by_contra h1 
        have h6 : (2 + 1 : ℝ) * (1 + A) = 0 := by
          linarith
        have h5 : 1 / ((2 + 1) * (1 + A)) = 0 := by
          rw [h6] 
          norm_num
        linarith [eq5, h5]
      have eq7 : 1 / ((2 + 1) * (1 + A)) = 1 / ((3 : ℝ) * (1 + A)) := by 
        ring_nf 
      rw [eq7] at eq5 
      have h2 : 1 + A ≠ 0 := by
        by_contra h3 
        have h4 : (1 + A) = 0 := by linarith 
        have h6 : (2 + 1 : ℝ) * (1 + A) = 0 := by 
          rw [show 1 + A = 0 by linarith] 
          norm_num 
        have h7 : (2 + 1 : ℝ) * (1 + A) ≠ 0 := h1 
        contradiction 
      field_simp [h2, show (6 : ℝ) ≠ 0 by norm_num] at eq5 ⊢ 
      <;> linarith 
    have eq7 : 1 + A = 2 := by 
      nlinarith 
    linarith

  have h1 : A = 1 := eq3 
  simp [hf, h1] 
  norm_num