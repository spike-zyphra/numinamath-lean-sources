import Mathlib

theorem number_theory_271471 (w x y z : ℕ)
    (hw : w = 2^129 * 3^81 * 5^128)
    (hx : x = 2^127 * 3^81 * 5^128)
    (hy : y = 2^126 * 3^82 * 5^128)
    (hz : z = 2^125 * 3^82 * 5^129) :
    x < y ∧ y < z ∧ z < w := by 
  rw [hw, hx, hy, hz]
  constructor
  · -- Show x < y
    norm_num
  constructor
  · -- Show y < z
    norm_num
  · -- Show z < w
    norm_num