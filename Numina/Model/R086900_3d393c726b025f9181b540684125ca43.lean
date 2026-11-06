import Mathlib

theorem algebra_296389 (a b c : ℝ) (h₀ : 3*a+7*b+c=3.15) (h₁ : 4*a+10*b+c=4.20) :
    a+b+c=1.05 := by
  have h2 : a + 3 * b = 1.05 := by
    calc
      a + 3 * b = (4 * a + 10 * b + c) - (3 * a + 7 * b + c) := by ring
      _ = 4.20 - 3.15 := by rw [h₁, h₀]
      _ = 1.05 := by norm_num
  have ha : a = 1.05 - 3 * b := by linarith
  rw [ha] at h₀
  have hc : c = 2 * b := by
    ring_nf at h₀ ⊢
    linarith
  rw [ha, hc]
  ring_nf