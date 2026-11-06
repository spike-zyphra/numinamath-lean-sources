import Mathlib

theorem number_theory_814 {x y z w : ℕ} (hx : x = 4002) (hy : y = 8004) (hz : z = 12006) (hw : w = 24012) :
    1 / 2001 = 1 / x + 1 / y + 1 / z + 1 / w := by 
  subst hx
  subst hy
  subst hz
  subst hw
  norm_num