import Mathlib

/- A positive number, if its fractional part, integer part, and the number itself form a geometric sequence, then the number is ___          ___. -/
theorem number_theory_9869 (x : ℝ) (hx : x > 0) (h : ∃ r, Int.fract x = r * x ∧ x = r * Int.floor x) :
    x = (1 + Real.sqrt 5) / 2 := by 
  rcases h with ⟨r, h1, h2⟩ 
  have h3 : Int.fract x = x - (Int.floor x : ℝ) := by
    rw [Int.fract]
    <;> simp 
  rw [h3] at h1
  have h4 : (Int.floor x : ℝ) = x * (1 - r) := by 
    nlinarith 
  have h5 : x = r * (Int.floor x : ℝ) := by 
    linarith 
  rw [show (Int.floor x : ℝ) = x * (1 - r) by linarith] at h5
  have h6 : x > 0 := hx 
  have h7 : x = r * x * (1 - r) := by 
    linarith 
  have h8 : r * x * (1 - r) = (x : ℝ) := by 
    linarith 
  have h9 : r * (1 - r) = 1 := by
    apply (mul_left_inj' (ne_of_gt h6)).mp
    linarith
  have h10 : r^2 - r + 1 = 0 := by 
    nlinarith 
  have h11 : (2 * r - 1)^2 < 0 := by 
    nlinarith [sq_nonneg (2 * r - 1), sq_nonneg (r - 1 / 2)]
  have h12 : (2 * r - 1)^2 ≥ 0 := by 
    apply sq_nonneg 
  linarith