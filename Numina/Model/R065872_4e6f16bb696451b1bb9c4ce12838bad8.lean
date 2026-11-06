import Mathlib

def f (n : ℕ) : ℕ := if (2 ∣ n ∧ 3 ∣ n) then 6 else (if (2 ∣ n) then 2 else 0)

theorem algebra_10610 (allie betty : ℕ)
    (ha : allie = f 5 + f 4 + f 1 + f 2)
    (hb : betty = f 6 + f 3 + f 3 + f 2) :
    allie * betty = 32 := by
  rw [ha, hb]
  norm_num [f]