import Mathlib

open Finset

theorem algebra_21743 :
    ((Finset.product (Icc 1 6) (Icc 1 6)).filter (fun x => (x.1 * 10 + x.2) % 8 = 0)).card / (Finset.product (Icc 1 6) (Icc 1 6)).card = (5 : ℚ) / 36 := by 
  have h1 : ((Finset.product (Icc 1 6) (Icc 1 6)).filter (fun x => (x.1 * 10 + x.2) % 8 = 0)).card = 5 := by
    native_decide
  have h2 : (Finset.product (Icc 1 6) (Icc 1 6)).card = 36 := by
    native_decide
  rw [h1, h2]
  all_goals norm_num