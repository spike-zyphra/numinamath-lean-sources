import Mathlib

theorem algebra_17234 (total_people : ℕ) (h : total_people = 30)
    (cool_dads : ℕ) (cool_moms : ℕ) (cool_dads_moms : ℕ)
    (h1 : cool_dads = 12) (h2 : cool_moms = 15) (h3 : cool_dads_moms = 9) :
    total_people - (cool_dads + cool_moms - cool_dads_moms) = 12 := by
  calc
    total_people - (cool_dads + cool_moms - cool_dads_moms)
        = 30 - (12 + 15 - 9) := by rw [h, h1, h2, h3]
    _ = 30 - (27 - 9) := by norm_num
    _ = 30 - 18 := by norm_num
    _ = 12 := by norm_num