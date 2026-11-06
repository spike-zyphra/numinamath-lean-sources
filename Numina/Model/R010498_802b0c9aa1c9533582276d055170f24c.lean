import Mathlib

theorem algebra_13154 {a b : ℤ} (ha : 0 < a) (hb : 0 < b)
    (h1 : a + b = 24) (h2 : 2 * a * b + 10 * a = 3 * b + 222) :
    a * b = 108 := by 
  have h3 : b = 24 - a := by linarith 
  rw [h3] at h2
  have h4 : 2 * a^2 - 61 * a + 294 = 0 := by
    nlinarith
  have h6 : (a - 6) * (2 * a - 49) = 0 := by 
    nlinarith
  cases (mul_eq_zero.mp h6) with
  | inl h1 =>
    have ha6 : a = 6 := by 
      linarith 
    have hb18 : b = 18 := by 
      linarith [h1, h3]
    rw [ha6, hb18]
    all_goals linarith
  | inr h2 =>
    have : a = 24 := by
      linarith 
    have hb0 : b = 0 := by 
      linarith [h1, this]
    linarith