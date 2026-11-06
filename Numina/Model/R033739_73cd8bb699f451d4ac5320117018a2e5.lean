import Mathlib

theorem algebra_13069 (f : ℝ → ℝ) (hf : f = fun x => (x - 20)^2 + 17)
    (a b c : ℝ) (ha : a = 4) (hb : b = 1) (hc : c = 311) :
    IsLeast {d | ∃ x, d = |a * x + b * f x + c| / Real.sqrt (a^2 + b^2)} (404 * Real.sqrt 17 / 17) := by
  have h1 : ∀ x, f x = (x - 20) ^ 2 + 17 := by 
    intro x 
    rw [hf]
  have ha4 : a = 4 := ha
  have hb1 : b = 1 := hb
  have hc311 : c = 311 := hc
  constructor 
  · -- Show that 404 * Real.sqrt 17 / 17 is achievable by some point on the parabola.
    use 18
    have eq1 : a * 18 + b * f 18 + c = 404 := by 
      rw [h1]
      rw [ha4, hb1, hc311]
      norm_num 
    have eq2 : Real.sqrt (a^2 + b^2) = Real.sqrt 17 := by 
      rw [ha4, hb1]
      norm_num
    have h_eq1 : |a * 18 + b * f 18 + c| / Real.sqrt (a^2 + b^2) = 404 * Real.sqrt 17 / 17 := by
      rw [eq1] 
      rw [eq2]
      have h_eq2 : |(404 : ℝ)| = (404 : ℝ) := by 
        norm_num 
      rw [h_eq2] 
      have h3 : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num) 
      have h5 : (404 / Real.sqrt 17 : ℝ) = (404 * Real.sqrt 17 / 17 : ℝ) := by
        have h6 : Real.sqrt 17 > 0 := by positivity 
        have h3 : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num) 
        field_simp [h6, h3]
        <;> nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)]
      have h6 : (404 : ℝ) / Real.sqrt 17 = (404 / Real.sqrt 17 : ℝ) := by ring 
      linarith [h5, h6]
    linarith [h_eq1]
  · -- Show that 404 * Real.sqrt 17 / 17 is indeed the smallest distance.
    intro d hd
    rcases hd with ⟨x, hx⟩ 
    have eq1 : f x = (x - 20) ^ 2 + 17 := h1 x 
    have eq2 : a * x + b * f x + c = x ^ 2 - 36 * x + 728 := by 
      rw [eq1] 
      rw [ha4, hb1, hc311] 
      ring 
    have eq3 : Real.sqrt (a^2 + b^2) = Real.sqrt 17 := by 
      rw [ha4, hb1] 
      norm_num 
    have hx1 : d = |x ^ 2 - 36 * x + 728| / Real.sqrt 17 := by 
      rw [show a * x + b * f x + c = x ^ 2 - 36 * x + 728 by linarith [eq2]] at hx
      rw [eq3] at hx 
      linarith 
    have h5 : x ^ 2 - 36 * x + 728 ≥ 404 := by 
      nlinarith [sq_nonneg (x - 18)]
    have h6 : |x ^ 2 - 36 * x + 728| ≥ 404 := by 
      cases abs_cases (x ^ 2 - 36 * x + 728) with
      | inl h =>
        linarith [show x ^ 2 - 36 * x + 728 ≥ 404 by linarith]
      | inr h =>
        nlinarith [show x ^ 2 - 36 * x + 728 ≥ 404 by linarith]
    have hx2 : d ≥ 404 * Real.sqrt 17 / 17 := by 
      rw [hx1]
      have h8 : Real.sqrt 17 > 0 := by positivity 
      have h9 : |x ^ 2 - 36 * x + 728| ≥ 404 := h6 
      have hx4 : |x ^ 2 - 36 * x + 728| / Real.sqrt 17 ≥ 404 / Real.sqrt 17 := by 
        apply (div_le_div_right (by positivity)).mpr 
        linarith 
      have h5' : (404 / Real.sqrt 17) = (404 * Real.sqrt 17 / 17) := by 
        have h6 : Real.sqrt 17 > 0 := by positivity 
        have h3 : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num) 
        field_simp [h6, h3]
        <;> nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)]
      linarith [hx4, h5']
    linarith