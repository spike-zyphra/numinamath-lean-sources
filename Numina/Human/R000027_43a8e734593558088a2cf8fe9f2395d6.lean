import Mathlib
open Nat


variable
  (Dad_step Masha_step Yasha_step : ℕ)
  (h_D_M : Dad_step * 5 = Masha_step * 3)
  (h_M_Y : Masha_step * 5 = Yasha_step * 3)
  (h_sum_M_Y : Masha_step + Yasha_step = 400)

include Dad_step h_D_M h_M_Y h_sum_M_Y in
/--
Dad, Masha, and Yasha are walking to school.
While Dad takes 3 steps, Masha takes 5 steps.
While Masha takes 3 steps, Yasha takes 5 steps.
Masha and Yasha counted that together they took 400 steps.
How many steps did Dad take?
-/
theorem combinatorics_4038 : Dad_step = 90 := by
  linarith
