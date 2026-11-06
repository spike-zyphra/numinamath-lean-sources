import Mathlib

theorem algebra_128311 (a b c d : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (a / b : ℚ) + (c / d : ℚ) ≠ (a + c) / (b + d) := by
  intro h
  have h1 : (a : ℚ) / (b : ℚ) + (c : ℚ) / (d : ℚ) = (a + c : ℚ) / (b + d : ℚ) := by
    simpa using h
  have h2 : (a : ℚ) * (d : ℚ) * (b + d : ℚ) + (c : ℚ) * (b : ℚ) * (b + d : ℚ) = (a + c : ℚ) * (b : ℚ) * (d : ℚ) := by
    have hb' : (b : ℚ) ≠ 0 := by
      exact_mod_cast show (b : ℤ) ≠ 0 by linarith
    have hd' : (d : ℚ) ≠ 0 := by
      exact_mod_cast show (d : ℤ) ≠ 0 by linarith
    have hb_add_d' : (b + d : ℚ) ≠ 0 := by
      exact_mod_cast show (b + d : ℤ) ≠ 0 by linarith
    field_simp [hb', hd', hb_add_d'] at h1 ⊢
    <;> nlinarith
  have h3 : (a : ℤ) * (d : ℤ) * (b + d : ℤ) + (c : ℤ) * (b : ℤ) * (b + d : ℤ) = (a + c : ℤ) * (b : ℤ) * (d : ℤ) := by
    exact_mod_cast h2
  have h4 : a * d^2 + c * b^2 = 0 := by
    nlinarith
  have h5 : a * d^2 > 0 := by
    apply mul_pos
    exact ha
    nlinarith
  have h7 : c * b^2 > 0 := by
    apply mul_pos
    exact hc
    nlinarith
  have h8 : a * d^2 + c * b^2 > 0 := by
    linarith
  linarith