import Mathlib

theorem algebra_1644 (v_a v_b x : ℝ) (h_v : v_b = 3 * v_a) (h_x : x > 0)
    (h_1 : 10 / v_a = x + 5 / v_b) (h_2 : 5 / v_b = x + 10 / v_a) :
    x = 8 := by
  have h1 : v_a ≠ 0 := by
    by_contra h
    have h4 : v_a = 0 := by linarith [h]
    rw [show v_a = 0 by linarith [h4]] at h_1 h_2
    norm_num [h_v] at h_1 h_2
    all_goals
      nlinarith -- h_x == x > 0 contradicts with x = 0 from 10 = 5
  rw [h_v] at h_1 h_2
  -- Equation 1: 10 / v_a = x + 5 / (3 * v_a)
  have eq1 : 10 / v_a = x + 5 / (3 * v_a) := by
    have h3 : v_a ≠ 0 := h1
    field_simp [h3]
    <;> ring_nf
    <;> nlinarith [sq_pos_of_ne_zero h3]
  -- Equation 2: 5 / (3 * v_a) = x + 10 / v_a
  have eq2 : 5 / (3 * v_a) = x + 10 / v_a := by
    have h3 : v_a ≠ 0 := h1
    field_simp [h3]
    <;> ring_nf
    <;> nlinarith [sq_pos_of_ne_zero h3]
  -- Solving the Equations
  nlinarith [sq_pos_of_ne_zero h1, h_x]