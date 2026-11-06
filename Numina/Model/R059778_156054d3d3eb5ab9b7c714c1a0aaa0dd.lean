import Mathlib

theorem algebra_275184 (a b c : ℝ) (ha : a ≠ 0) (h : a - b + c = 0)
    (f : ℝ → ℝ) (hf : f = fun x => 3 * a * x ^ 2 - 2 * b * x + c)
    (h0 : f 0 > 0) (h1 : f 1 > 0) :
    4 / 3 < (a + 3 * b + 7 * c) / (2 * a + b) ∧
    (a + 3 * b + 7 * c) / (2 * a + b) < 7 / 2 := by 
  have hc : c = b - a := by linarith 
  have h2 : c > 0 := by 
    rw [hf] at h0 
    simp at h0 
    nlinarith 
  have h1' : 3 * a - 2 * b + c > 0 := by 
    rw [hf] at h1 
    simp at h1 
    nlinarith 
  have h3 : b > a := by 
    nlinarith [hc]
  have h4 : b < 2 * a := by 
    nlinarith [hc]
  have h5 : a > 0 := by nlinarith 
  have h6 : b > 0 := by nlinarith 
  have h9 : (a + 3 * b + 7 * c) = 10 * b - 6 * a := by 
    rw [show c = b - a by linarith [hc]]
    ring 
  have h10 : (2 * a + b) > 0 := by 
    nlinarith 
  have h11 : (a + 3 * b + 7 * c) / (2 * a + b) = (10 * b - 6 * a) / (2 * a + b) := by 
    rw [h9] 
  have h12 : (10 * b - 6 * a) / (2 * a + b) > 4 / 3 := by 
    apply (lt_div_iff₀ (by nlinarith)).mpr 
    nlinarith 
  have h13 : (10 * b - 6 * a) / (2 * a + b) < 7 / 2 := by 
    apply (div_lt_iff₀ (by nlinarith)).mpr 
    nlinarith 
  rw [h11] 
  constructor 
  · linarith 
  · linarith