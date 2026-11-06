import Mathlib
open Finset Nat
noncomputable section

/-A line of soldiers 1 mile long is jogging. The drill sergeant, in a car, moving at twice their speed, repeatedly drives from the back of the line to the front of the line and
back again. When each soldier has marched 15 miles, how much mileage has been added to the car, to the nearest mile?-/
theorem logic_and_puzzles_610922 
    (v_s v_c t : ℝ) (hv_s : v_s > 0) (h_v_c : v_c = 2 * v_s) (h_t : t = 15 / v_s) :
    v_c * t = 30 := by
  -- Use car speed definition.
  have h_v_c_apply : v_c = 2 * v_s := h_v_c
  -- Use time definition.
  have h_t_apply : t = 15 / v_s := h_t
  -- Express car distance.
  have h_D_c : v_c * t = (2 * v_s) * (15 / v_s) := by
    rw [h_v_c_apply, h_t_apply]
  -- Simplify the expression.
  have h_simplify : (2 * v_s) * (15 / v_s) = 2 * 15 := by
    rw [mul_assoc, mul_comm v_s (15 / v_s)]
    have h_div_cancel : v_s * (15 / v_s) = 15 := by
      apply mul_div_cancel₀
      apply ne_of_gt hv_s
    rw [mul_comm (15 / v_s), h_div_cancel, mul_comm]
  -- Compute final value.
  have h_final : (2 : ℝ ) * 15 = 30 := by norm_num
  rw [h_D_c, h_simplify, h_final]
