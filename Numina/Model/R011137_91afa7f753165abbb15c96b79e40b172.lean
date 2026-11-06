import Mathlib

theorem algebra_97876 {x red blue: ℕ} (hred: red = (0.36:ℝ)*100) (htot: 100 = red + blue) (h: blue - x = (0.72:ℝ) * (red + blue - x))  :
x = 50 := by
  have h1 : red = 36 := by
    have eq1 : (red : ℝ) = 36 := by
      rw [hred]
      norm_num
    exact_mod_cast eq1
  have h2 : blue = 64 := by
    omega
  have h3 : (64 : ℝ) - (↑x : ℝ) = (0.72 : ℝ) * ((36 : ℝ) + (64 : ℝ) - ↑x) := by 
    rw [show (red : ℝ) = (36 : ℝ) by exact_mod_cast h1] at h
    rw [show (blue : ℝ) = (64 : ℝ) by exact_mod_cast h2] at h
    simpa using h
  have eq1 : (x : ℝ) = (50 : ℝ) := by 
    ring_nf at h3
    have eq2 : (x : ℝ) = (50 : ℝ) := by
      nlinarith
    linarith
  have eq2 : x = 50 := by 
    exact_mod_cast eq1
  exact eq2