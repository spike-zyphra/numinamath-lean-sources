import Mathlib

theorem algebra_7598 {a b c : ℝ} {f : ℝ → ℝ} 
    (hf : ∀x, f x = a * x^2 + b * x + c) (ha : a ≠ 0) 
    (h1 : f 13 = 0) (h2 : f 3 = 0) (h3 : f 10 = 1.4) :
    f = fun x ↦ (-1/15) * x^2 + (16/15) * x + (-13/5) := by 
  rw [hf] at *
  have h4 : a = -1 / 15 := by
    ring_nf at h1 h2 h3 ⊢
    norm_num at h1 h2 h3 ⊢
    linarith
  have h5 : b = 16 / 15 := by 
    ring_nf at h1 h2 h3 ⊢
    norm_num at h1 h2 h3 ⊢
    linarith
  have h6 : c = -13 / 5 := by 
    ring_nf at h1 h2 h3 ⊢
    norm_num at h1 h2 h3 ⊢
    linarith
  ext x
  rw [←h4, ←h5, ←h6]
  exact hf x