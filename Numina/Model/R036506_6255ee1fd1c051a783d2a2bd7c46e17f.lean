import Mathlib

theorem algebra_290114 {a b c d : ℝ} (f : ℝ → ℝ) (hf : f = fun x => x^4 + a*x^3 + b*x^2 + c*x + d)
    (h1 : f 4 = 102) (h2 : f 3 = 102) (h3 : f (-3) = 102) (h4 : f (-4) = 102) :
    f 0 = 246 ∧ f 5 = 246 ∧ f (-5) = 246 := by

  have eq1 : 4 ^ 4 + a * 4 ^ 3 + b * 4 ^ 2 + c * 4 + d = 102 := by
    rw [hf] at h1
    simpa using h1
  have eq2 : 3 ^ 4 + a * 3 ^ 3 + b * 3 ^ 2 + c * 3 + d = 102 := by
    rw [hf] at h2
    simpa using h2
  have eq3 : (-3) ^ 4 + a * (-3) ^ 3 + b * (-3) ^ 2 + c * (-3) + d = 102 := by
    rw [hf] at h3
    simpa using h3
  have eq4 : (-4) ^ 4 + a * (-4) ^ 3 + b * (-4) ^ 2 + c * (-4) + d = 102 := by
    rw [hf] at h4
    simpa using h4
  have ha : a = 0 := by
    linarith
  have hb : b = -25 := by
    have h1' : 154 + 64 * a + 16 * b + 4 * c + d = 0 := by linarith
    have h4' : 154 - 64 * a + 16 * b - 4 * c + d = 0 := by linarith
    rw [ha] at h1' h4'
    linarith
  have hc : c = 0 := by
    have h2' : -21 + 27 * a + 9 * b + 3 * c + d = 0 := by linarith
    have h3' : -21 - 27 * a + 9 * b - 3 * c + d = 0 := by linarith
    rw [ha, hb] at h2' h3'
    linarith
  have hd : d = 246 := by
    have h2' : -21 + 27 * a + 9 * b + 3 * c + d = 0 := by linarith
    rw [ha, hb, hc] at h2'
    linarith
  constructor
  · -- Show that f 0 = 246
    rw [hf]
    simp [ha, hb, hc, hd]
    <;> nlinarith
  constructor
  · -- Show that f 5 = 246
    rw [hf]
    simp [ha, hb, hc, hd]
    <;> nlinarith
  · -- Show that f (-5) = 246
    rw [hf]
    simp [ha, hb, hc, hd]
    <;> nlinarith