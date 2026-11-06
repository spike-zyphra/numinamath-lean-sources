import Mathlib

theorem algebra_172035 {a : ℕ → ℝ} (ha : ∀ n ≥ 2, a n = (a (n - 1) + a (n + 1)) / 4)
    (ha1 : a 1 = 1) (ha9 : a 9 = 40545) :
    a 25 = 57424611447841 := by
  have eq3 := ha 2 (by norm_num)
  norm_num at eq3
  have eq4 := ha 3 (by norm_num)
  norm_num at eq4
  have eq5 := ha 4 (by norm_num)
  norm_num at eq5
  have eq6 := ha 5 (by norm_num)
  norm_num at eq6
  have eq7 := ha 6 (by norm_num)
  norm_num at eq7
  have eq8 := ha 7 (by norm_num)
  norm_num at eq8
  have eq9 := ha 8 (by norm_num)
  norm_num at eq9
  have eq10 := ha 9 (by norm_num)
  norm_num at eq10
  have eq11 := ha 10 (by norm_num)
  norm_num at eq11
  have eq12 := ha 11 (by norm_num)
  norm_num at eq12
  have eq13 := ha 12 (by norm_num)
  norm_num at eq13
  have eq14 := ha 13 (by norm_num)
  norm_num at eq14
  have eq15 := ha 14 (by norm_num)
  norm_num at eq15
  have eq16 := ha 15 (by norm_num)
  norm_num at eq16
  have eq17 := ha 16 (by norm_num)
  norm_num at eq17
  have eq18 := ha 17 (by norm_num)
  norm_num at eq18
  have eq19 := ha 18 (by norm_num)
  norm_num at eq19
  have eq20 := ha 19 (by norm_num)
  norm_num at eq20
  have eq21 := ha 20 (by norm_num)
  norm_num at eq21
  have eq22 := ha 21 (by norm_num)
  norm_num at eq22
  have eq23 := ha 22 (by norm_num)
  norm_num at eq23
  have eq24 := ha 23 (by norm_num)
  norm_num at eq24
  have eq25 := ha 24 (by norm_num)
  norm_num at eq25
  norm_num [ha1, ha9] at *
  linarith