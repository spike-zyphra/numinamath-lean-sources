import Mathlib

theorem algebra_175122 (v1 v2 v3 t1 t2 t3 : ℝ) 
    (h1 : v1 > 0) (h2 : v2 > 0) (h3 : v3 > 0)
    (h4 : t1 > 0) (h5 : t2 > 0) (h6 : t3 > 0) 
    (h7 : v2 < v1) (h8 : v1 < v3)
    (h9 : v1 = 80) (h10 : v2 = 60) 
    (h11 : t1 = 1) (h12 : t2 = 1) (h13 : t3 = 2)
    (h_overtake : ∃ (x : ℝ), x > 0 ∧ v1 * (t1 + x) = v3 * x)
    (h_arrival : ∀ x > 0, v1 * (t1 + x) = v3 * x → 
        ∃ (d : ℝ), d > 0 ∧ d = v3 * (x + t2) ∧ d = v2 * (t1 + x + t2 + t3)) :
    ∃ (d : ℝ) (x : ℝ), d = 360 ∧ v3 = 120 ∧ x = 2 := by

  rcases h_overtake with ⟨x, hx1, beq⟩
  have h19 := h_arrival x hx1 beq

  rcases h19 with ⟨d, hd0, heq1, heq2⟩

  simp only [show t2 = (1 : ℝ) by linarith [h12]] at heq1
  simp only [show t1 = (1 : ℝ) by linarith [h11], 
          show t2 = (1 : ℝ) by linarith [h12], 
          show t3 = (2 : ℝ) by linarith [h13]] at heq2

  rw [show v2 = (60 : ℝ) by linarith [h10]] at heq2

  have eq3 : v1 * (t1 + x) = v3 * x := beq 
  simp only [show v1 = (80 : ℝ) by linarith [h9], 
      show t1 = (1 : ℝ) by linarith [h11]] at eq3

  have eq4 : x = (2 : ℝ) := by
    nlinarith [sq_nonneg (x - (2 : ℝ)), sq_nonneg (v3 - (120 : ℝ)), mul_pos h1 h3]

  have eq5 : v3 = (120 : ℝ) := by
    rw [show x = (2 : ℝ) by linarith [eq4] ] at eq3
    nlinarith

  have eq7 : d = (360 : ℝ) := by
    rw [eq5, eq4] at heq1
    nlinarith
  exact ⟨d, x, by linarith [eq7], by linarith [eq5], by linarith [eq4]⟩