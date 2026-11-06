import Mathlib

theorem algebra_196613 {x y z t : ℝ} (hx : x > 0 ∧ x ≠ 1) (hy : y > 0 ∧ y ≠ 1) (hz : z > 0 ∧ z ≠ 1)
    (ht : t > 0) (h₁ : Real.logb x t = 6) (h₂ : Real.logb y t = 10) (h₃ : Real.logb z t = 15)
    (d : ℝ) (hd : d = Real.logb (x * y * z) t) : d = 3 := by
  have h₄ : Real.logb x t = Real.log t / Real.log x := by
    field_simp [Real.logb]
  rw [h₄] at h₁
  have h₅ : Real.logb y t = Real.log t / Real.log y := by
    field_simp [Real.logb]
  rw [h₅] at h₂
  have h₆ : Real.logb z t = Real.log t / Real.log z := by
    field_simp [Real.logb]
  rw [h₆] at h₃
  have h₇ : Real.logb (x * y * z) t = Real.log t / Real.log (x * y * z) := by
    field_simp [Real.logb]
  rw [h₇] at hd
  have h8 : Real.log t = 6 * Real.log x := by 
    have h₄ : Real.log x ≠ 0 := by 
      by_contra h
      have : x = 1 := by 
        rw [Real.log_eq_zero] at h
        rcases h with (r | r | r)
        · linarith 
        · linarith 
        · linarith 
      have h4 : x = 1 := by linarith 
      tauto 
    field_simp at h₁ ⊢ 
    linarith
  have h9 : Real.log t = 10 * Real.log y := by
    have h₅ : Real.log y ≠ 0 := by 
      by_contra h
      have : y = 1 := by 
        rw [Real.log_eq_zero] at h
        rcases h with (r | r | r)
        · linarith 
        · linarith 
        · linarith 
      have h4 : y = 1 := by linarith 
      tauto 
    field_simp at h₂ ⊢ 
    linarith
  have h10 : Real.log t = 15 * Real.log z := by
    have h₆ : Real.log z ≠ 0 := by 
      by_contra h
      have : z = 1 := by 
        rw [Real.log_eq_zero] at h
        rcases h with (r | r | r)
        · linarith 
        · linarith 
        · linarith 
      have h4 : z = 1 := by linarith 
      tauto 
    field_simp at h₃ ⊢ 
    linarith
  have h11 : Real.log y = (3 / 5) * Real.log x := by
    linarith
  have h12 : Real.log z = (2 / 5) * Real.log x := by
    linarith
  have h13 : Real.log (x * y * z) = Real.log x + Real.log y + Real.log z := by
    simp [Real.log_mul, hx.1.ne.symm, hy.1.ne.symm, hz.1.ne.symm]
  have h14 : Real.log (x * y * z) = 2 * Real.log x := by 
    rw [h13, h11, h12]
    linarith
  have h15 : Real.log x ≠ 0 := by
    by_contra h
    have h0 : Real.log x = 0 := by linarith
    have h1 : Real.log t = 0 := by 
      linarith [h8, h0]
    have h2 : Real.log t / Real.log x = 0 := by
      rw [h0]
      norm_num
    linarith [h₁, h2]
  rw [hd]
  have h16 : Real.log t / Real.log (x * y * z) = 3 := by
    rw [h14]
    have h17 : Real.log (x * y * z) ≠ 0 := by 
      intro h
      have h0 : Real.log x = 0 := by 
        linarith [h14, h]
      contradiction 
    have h15' : Real.log x ≠ 0 := h15
    field_simp [h15', h17] at *
    linarith [h8, h14]
  exact h16