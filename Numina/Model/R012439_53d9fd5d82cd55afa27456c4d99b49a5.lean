import Mathlib

theorem algebra_130552 {a b c : ℝ} (p : ℝ → ℝ) (hp : ∀ x, |x| ≤ 1 → |p x| ≤ 1)
    (h : p = fun x => a * x ^ 2 + b * x + c) :
    ∀ x, |x| ≤ 1 → |c * x ^ 2 + b * x + a| ≤ 2 := by 
  intro x hx
  have h1 := hp 1 (by norm_num)
  have h2 := hp (-1) (by norm_num)
  have h3 := hp 0 (by norm_num)
  simp [h] at h1 h2 h3
  have h4 : -1 ≤ a - b + c := by linarith [abs_le.mp h2]
  have h5 : a - b + c ≤ 1 := by linarith [abs_le.mp h2]
  have h6 : -1 ≤ a + b + c := by linarith [abs_le.mp h1]
  have h7 : a + b + c ≤ 1 := by linarith [abs_le.mp h1]
  have h8 : -1 ≤ c := by linarith [abs_le.mp h3]
  have h9 : c ≤ 1 := by linarith [abs_le.mp h3]
  have h10 : -1 ≤ x := by 
    cases' abs_le.mp hx with h11 h12
    linarith
  have h11 : x ≤ 1 := by 
    cases' abs_le.mp hx with h11 h12
    linarith
  have h12 : x ^ 2 ≤ 1 := by
    nlinarith
  have h13 : -2 ≤ c * x ^ 2 + b * x + a := by
    nlinarith [abs_le.mp h1, abs_le.mp h2, abs_le.mp h3, 
      mul_nonneg (show (0 : ℝ) ≤ 1 - x by linarith) (show (0 : ℝ) ≤ x + 1 by linarith), 
      mul_nonneg (show (0 : ℝ) ≤ x + 1 by linarith) (show (0 : ℝ) ≤ 1 - x by linarith)]
  have h14 : c * x ^ 2 + b * x + a ≤ 2 := by
    nlinarith [abs_le.mp h1, abs_le.mp h2, abs_le.mp h3, 
      mul_nonneg (show (0 : ℝ) ≤ 1 - x by linarith) (show (0 : ℝ) ≤ x + 1 by linarith), 
      mul_nonneg (show (0 : ℝ) ≤ x + 1 by linarith) (show (0 : ℝ) ≤ 1 - x by linarith)]
  apply abs_le.mpr
  constructor
  · linarith
  · linarith