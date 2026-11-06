import Mathlib

theorem algebra_173091 (a p m : ℝ) (h₀ : 5*a+4*p=48) (h₁ : 2*a+3*m=33)
    (h₂ : m=p+2.5) :
    3*a+3*p=31.5 := by
  rw [h₂] at h₁
  ring_nf at h₁ 
  linarith