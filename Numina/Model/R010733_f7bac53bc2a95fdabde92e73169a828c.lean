import Mathlib
open Real
theorem algebra_97260 (s c p : ℝ) (h1 : 3*s+7*c+p=3.15) (h2 : 4*s+10*c+p=4.20) : s+c+p=1.05 := by
  have h3 : s + 3 * c = 1.05 := by 
    calc 
      s + 3 * c = (4 * s + 10 * c + p) - (3 * s + 7 * c + p) := by ring
      _ = 4.20 - 3.15 := by rw [h2, h1]
      _ = 1.05 := by norm_num
  have h4 : p = 2 * c := by
    have hs : s = 1.05 - 3 * c := by linarith
    rw [hs] at h1
    ring_nf at h1
    linarith
  linarith [h3, h4]