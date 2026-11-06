import Mathlib

theorem inequalities_227706 :
    ¬∃ x y z t : ℝ, |y - z + t| < |x| ∧ |x - z + t| < |y| ∧ |x - y + t| < |z| ∧ |x - y + z| < |t|
  := by 
  rintro ⟨x, y, z, t, h1, h2, h3, h4⟩
  have h11 : (y - z + t) ^ 2 < x^2 := by 
    have h1a : |y - z + t| < |x| := h1
    cases' abs_cases (y - z + t) with h111 h111 <;> 
      cases' abs_cases x with h22 h22 <;> 
        nlinarith [sq_nonneg (x - (y - z + t)), sq_nonneg (x + (y - z + t))]
  have h22 : (x - z + t) ^ 2 < y^2 := by 
    have h1a : |x - z + t| < |y| := h2 
    cases' abs_cases (x - z + t) with h111 h111 <;> 
      cases' abs_cases y with h22 h22 <;> 
        nlinarith [sq_nonneg (y - (x - z + t)), sq_nonneg (y + (x - z + t))]
  have h33 : (x - y + t) ^ 2 < z^2 := by 
    have h1a : |x - y + t| < |z| := h3 
    cases' abs_cases (x - y + t) with h111 h111 <;> 
      cases' abs_cases z with h22 h22 <;> 
        nlinarith [sq_nonneg (z - (x - y + t)), sq_nonneg (z + (x - y + t))]
  have h44 : (x - y + z) ^ 2 < t^2 := by 
    have h1a : |x - y + z| < |t| := h4 
    cases' abs_cases (x - y + z) with h111 h111 <;> 
      cases' abs_cases t with h22 h22 <;> 
        nlinarith [sq_nonneg (t - (x - y + z)), sq_nonneg (t + (x - y + z))]
  nlinarith [sq_nonneg (x - y + 0), sq_nonneg (z - t + 0), sq_nonneg ((x - y + z) - (x - y + t)), 
      sq_nonneg ((x - y + t) - (x - z + t)), 
      sq_nonneg ((x - z + t) - (y - z + t)), 
      sq_nonneg ((x - y + z) - z)]