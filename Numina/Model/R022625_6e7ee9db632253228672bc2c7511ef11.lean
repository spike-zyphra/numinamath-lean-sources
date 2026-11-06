import Mathlib

open Real

theorem algebra_93316 {k : ℝ} (hk : ∃ x y, x > 0 ∧ y > 0 ∧ logb 5 x = k ∧ logb 5 (x + 4) = k - 0.5) :
    ∃ a b : ℤ, k = a + sqrt b ∧ a + b = 6 := by 
  rcases hk with ⟨x, y, hx1, hx2, h1, h2⟩
  have h3 : logb 5 x - logb 5 (x + 4) = 0.5 := by
    have h4 : logb 5 (x + 4) = k - 0.5 := h2
    have h5 : logb 5 x = k := h1
    linarith
  have h4 : logb 5 x - logb 5 (x + 4) = logb 5 (x / (x + 4)) := by
    rw [logb_div (by linarith) (by linarith)]
  rw [h4] at h3
  have h5 : x / (x + 4) = (5 : ℝ) ^ (0.5 : ℝ) := by
    have h6 : logb 5 (x / (x + 4)) = (0.5 : ℝ) := by
      linarith
    rw [logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by
      apply div_pos
      linarith
      linarith)] at h6
    · linarith
    all_goals linarith
  have h6 : (x / (x + 4)) < (1 : ℝ) := by
    have hx7 : x > 0 := hx1
    have hx8 : x + 4 > x := by
      linarith
    have hx9 : x / (x + 4) < 1 := by
      have h11 : x + 4 > x := hx8
      have h15 : x / (x + 4) < (x + 4) / (x + 4) := by
        apply (div_lt_div_right (by linarith)).mpr
        linarith
      have h10 : (x + 4) / (x + 4) = 1 := by
        field_simp
      nlinarith [h10]
    linarith
  have h7 : (5 : ℝ) ^ (0.5 : ℝ) > (1 : ℝ) := by
    have h8 : (5 : ℝ) ^ (0.5 : ℝ) > (1 : ℝ) := by
      have h51 : (1 : ℝ) < (5 : ℝ) := by norm_num
      have h52 : (1 : ℝ) < (5 : ℝ) ^ (0.5 : ℝ) := by
        have h53 : (1 : ℝ) = (5 : ℝ) ^ (0 : ℝ) := by
          simp
        rw [h53]
        apply Real.rpow_lt_rpow_of_exponent_lt 
        all_goals norm_num
      linarith
    linarith
  have h8 : (x / (x + 4)) > (1 : ℝ) := by
    linarith [h5, h7]
  nlinarith