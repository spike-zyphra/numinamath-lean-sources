import Mathlib

theorem algebra_93930 (p q : ℝ) (h₁: 9 = p + d) (h₂: 3 * p - q = 9 + d)  (h₃: 3 * p + q = 3 * p - q + d) :
p + 2009 * d = 8041 := by
  have hp : p = 9 - d := by linarith
  have hq : q = d / 2 := by
    linarith
  rw [hp, hq] at h₂
  have hd : d = 4 := by 
    linarith
  have hp' : p = 5 := by 
    rw [hd] at hp
    linarith
  rw [hp', hd]
  norm_num