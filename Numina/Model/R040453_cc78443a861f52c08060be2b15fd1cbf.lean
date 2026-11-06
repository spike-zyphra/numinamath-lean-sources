import Mathlib

theorem algebra_129127 {a b c d x : ℝ} (h₀ : a ≠ c) (h₁ : a + d = 2015) (h₂ : b + c = 2015)
    (h₃ : (x - a) * (x - b) = (x - c) * (x - d)) :
    x = 1007.5 := by
  have h4 : d = 2015 - a := by
    linarith 
  have h5 : b = 2015 - c := by
    linarith 
  rw [show b = 2015 - c by linarith] at h₃
  rw [show d = 2015 - a by linarith] at h₃
  have eq3 : 2 * (c - a) * x + 2015 * (a - c) = 0 := by
    ring_nf at h₃ ⊢
    linarith 
  have h6 : c - a ≠ 0 := by 
    intro h
    apply h₀
    linarith
  have eq4 : 2 * (c - a) * x = 2015 * (c - a) := by
    linarith [eq3]
  have hx : x = (2015 / 2 : ℝ) := by 
    apply (mul_left_inj' h6).mp
    linarith 
  rw [hx]
  all_goals norm_num