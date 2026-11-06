import Mathlib

theorem algebra_14790 {bio chem both : ℕ} (h1 : bio = 8)
  (h2 : both = 4) (h3 : bio + chem - both = 20) :
  chem = 16 := by 
  omega