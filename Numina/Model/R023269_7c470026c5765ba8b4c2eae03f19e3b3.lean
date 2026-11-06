import Mathlib

theorem algebra_298786 {a b c : ℕ} (ha : 0 < a) (hsum : a + b + c ≥ 1) (hc : c ≥ 1)
    (hroots : ∃ x1 x2 : ℝ, x1 ≠ x2 ∧ x1 > 0 ∧ x2 > 0 ∧ x1 < 1 ∧ x2 < 1 ∧
      a * x1 ^ 2 + b * x1 + c = 0 ∧ a * x2 ^ 2 + b * x2 + c = 0) :
    a ≥ 5 := by
  rcases hroots with ⟨x1, x2, hx12, hx1, hx2, hx11, hx21, h1, h2⟩
  have eq1 : (a : ℝ) * x1 ^ 2 + (b : ℝ) * x1 + (c : ℝ) = (0 : ℝ) := by
    exact_mod_cast h1
  have eq2 : (a : ℝ) * x2 ^ 2 + (b : ℝ) * x2 + (c : ℝ) = (0 : ℝ) := by
    exact_mod_cast h2
  have eq3 : (a : ℝ) * (x1 ^ 2 - x2 ^ 2) + (b : ℝ) * (x1 - x2) = 0 := by
    nlinarith 
  have eq4 : (a : ℝ) * (x1 + x2) + (b : ℝ) = 0 := by
    apply (mul_left_inj' (show x1 - x2 ≠ 0 by
      intro h
      apply hx12
      linarith
    )).mp 
    linarith [eq3]
  by_contra h
  push_neg at h
  have ha' : a < 5 := by
    omega
  have h4 : a ≤ 4 := by 
    omega
  have ha'1 : (a : ℝ) ≤ (4 : ℝ) := by 
    exact_mod_cast h4
  have h5 : (0 : ℝ) < x1 := by linarith 
  have h6 : (0 : ℝ) < x2 := by linarith 
  have h7 : x1 < 1 := by linarith 
  have h8 : x2 < 1 := by linarith 
  interval_cases a <;> norm_num at h1 h2 hsum hc 
  <;> nlinarith [mul_pos (show (0 : ℝ) < x1 by linarith) (show (0 : ℝ) < x2 by linarith), 
      mul_pos (show (0 : ℝ) < x1 by linarith) (show (0 : ℝ) < (1 - x1) by linarith), 
      mul_pos (show (0 : ℝ) < x2 by linarith) (show (0 : ℝ) < (1 - x2) by linarith), 
      sq_pos_of_ne_zero (show (x1 - x2) ≠ 0 by
        intro h
        apply hx12
        linarith 
      ), sq_nonneg (x1 - x2)]