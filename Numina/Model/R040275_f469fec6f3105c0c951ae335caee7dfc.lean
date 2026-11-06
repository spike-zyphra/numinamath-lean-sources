import Mathlib


open Nat


theorem number_theory_154055 (F : ℕ → ℕ)
    (hF : ∀ n, F (n + 2) = F (n + 1) + F n)
    (hF0 : F 0 = 0) (hF1 : F 1 = 1) :
    ∃ n, 0 < n ∧ 2007 ∣ F n := by 
  use 1344
  constructor
  · -- Show that 1344 > 0
    norm_num
  · -- Show that 2007 divides F 1344
    set_option maxRecDepth 200000 in
    norm_num [hF0, hF1, hF]