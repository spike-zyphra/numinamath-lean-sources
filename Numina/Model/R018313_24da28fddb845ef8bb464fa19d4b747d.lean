import Mathlib

theorem number_theory_189739 (x y : ℚ) (hx : x.num > 0) (hy : y.num > 0)
    (hxy : x.num + y.num = 9 ∧ x.den + y.den = 10) :
    x + y ≤ 73 / 9 := by
  rcases hxy with ⟨h1, h2⟩
  have h8 : x = (x.num : ℚ) / x.den := by
    field_simp [Rat.den_ne_zero]
    <;> linarith
  have h9 : y = (y.num : ℚ) / y.den := by
    field_simp [Rat.den_ne_zero]
    <;> linarith
  rw [h8, h9]
  have h16 : x.num ≤ 9 := by omega
  have h17 : y.num ≤ 9 := by omega
  have h18 : x.den ≤ 10 := by omega
  have h19 : y.den ≤ 10 := by omega
  norm_num at h1 h2 ⊢
  interval_cases h : x.num <;> interval_cases k : y.num <;> interval_cases l : x.den <;> interval_cases m : y.den
  <;> norm_num at h1 h2 ⊢
  <;> tauto