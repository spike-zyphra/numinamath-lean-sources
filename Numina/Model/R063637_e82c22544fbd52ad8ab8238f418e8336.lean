import Mathlib

theorem number_theory_1160 {p q r s : ℕ}
    (hp : p = 3^70) (hq : q = 5^56) (hr : r = 6^42) (hs : s = 17^28) :
    max (max p q) (max r s) = q := by
  rw [hp, hq, hr, hs]
  norm_num [max_assoc, max_comm, max_left_comm]