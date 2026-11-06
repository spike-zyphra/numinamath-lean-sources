import Mathlib

theorem algebra_95525 (a b c d : ℚ)
    (ha : a = 1 / 5) (hb : b = 1 / 3) (hc : c = 1 / 4)
    (hd : d = 1 - a - b - c) :
    b > c ∧ c > d ∧ d > a := by

  rw [ha] at hd
  rw [hb] at hd
  rw [hc] at hd
  have h1 : d = 13 / 60 := by 
    norm_num at hd ⊢
    linarith

  constructor
  · -- Show b > c
    rw [hb, hc]
    norm_num

  constructor
  · -- Show c > d
    rw [hc, h1]
    norm_num

  · -- Show d > a
    rw [h1, ha]
    norm_num