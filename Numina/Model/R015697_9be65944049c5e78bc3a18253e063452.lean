import Mathlib

theorem algebra_11242 (avg_beats : ℕ → ℕ) (h : ∀ x, avg_beats x = x * 150) (d : ℕ) (hd : d = 26)
    (v : ℕ) (hv : v = 5 * d) : avg_beats v = 19500 := by 
  subst hd
  subst hv
  simp [h]
  all_goals norm_num