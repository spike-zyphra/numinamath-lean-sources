import Mathlib

/- Suppose $x \in [-5,-3]$ and $y \in [2,4]$. What is the largest possible value of $\frac{x+y}{x-y}$? -/
theorem algebra_22531 :
    IsGreatest {a | ∃ (x:ℝ) (y:ℝ) , x ∈ Set.Icc (-5) (-3) ∧ y ∈ Set.Icc 2 4 ∧ a = (x + y) / (x - y)}  (3 / 7) := by
  unfold IsGreatest
  constructor
  -- exist x and y so that (x + y) / (x - y) = 3 / 7
  . {
    simp
    use -5
    simp
    constructor
    linarith
    use 2
    simp
    constructor
    linarith
    ring_nf
  }
  . {
    unfold upperBounds
    simp
    intro a x x_low x_up y y_low y_up ha

    have y_inv_low : 1 / y ≤ 1 / 2 := one_div_le_one_div_of_le (by linarith) y_low
    have y_inv_up :  1 / 4 ≤ 1 / y := one_div_le_one_div_of_le (by linarith) y_up

    -- Substitute and calculate the range
    let k := x / y
    have k_low : -5 / 2 ≤ k := by
      simp [k];
      nth_rw 2 [div_eq_mul_one_div];
      nth_rw 1 [div_eq_mul_one_div];
      exact mul_le_mul_of_nonpos_of_nonneg x_low y_inv_low (by linarith) (by linarith)
    have k_up : k ≤ -3 / 4 := by
      simp [k];
      nth_rw 2 [div_eq_mul_one_div];
      nth_rw 1 [div_eq_mul_one_div];
      exact mul_le_mul_of_nonpos_of_nonneg x_up y_inv_up (by linarith) (by linarith)
    have k_ne_1 : k - 1 ≠ 0 := by linarith

    -- use k to simplify a
    replace ha : a = (k + 1) / (k - 1) := by
      simp [k]
      rw [ha]
      have hy: y ≠ 0 := by linarith
      rw [<-(mul_div_mul_right (x / y + 1) (x / y - 1) hy)]
      rw [right_distrib, sub_mul]
      simp [hy]
    replace ha : a = 1 + 2 / (k - 1) :=
      calc a = (k + 1) / (k - 1) := by rw [ha]
          _ = ((k - 1) + 2) / (k - 1) := by ring_nf
          _ = (k - 1)/(k - 1) + 2 / (k - 1) := by ring_nf
          _ = 1 + 2 / (k - 1) := by simp [k_ne_1]
    rw [
      ha,
      <-add_le_add_iff_left (-1:ℝ),
      <-add_assoc,
      neg_add_cancel,
      zero_add,
      <- (mul_le_mul_iff_of_pos_left (by linarith : 0<1/(2:ℝ))),
      mul_div,
      one_div_mul_cancel (by linarith),
      one_div_le_of_neg (by linarith) (by linarith),
      <-add_le_add_iff_right (1:ℝ),
      sub_add_cancel
    ]
    ring_nf
    exact k_low
  }
