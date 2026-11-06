import Mathlib

theorem number_theory_4821 :
    ∃ n : ℕ, n > 0 ∧ n ^ n = 827240261886336764177 := by 
  use 17
  constructor
  · norm_num -- proves 17 > 0
  · norm_num -- proves 17 ^ 17 = 827240261886336764177