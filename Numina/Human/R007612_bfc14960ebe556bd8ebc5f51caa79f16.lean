import Mathlib

/--
If $a,b,c$ are real numbers such that $a^2 + 2b =7$, $b^2 + 4c= -7,$ and $c^2 + 6a= -14$, find $a^2 + b^2 + c^2.$
$\text{(A) }14 \qquad \text{(B) }21 \qquad \text{(C) }28 \qquad \text{(D) }35 \qquad \text{(E) }49$
-/

theorem algebra_1136
  (a b c : ℝ ) (h1 : a ^ 2 + 2 * b  = 7) (h2 : b^2 + 4 * c = -7) (h3 : c^2 + 6 * a = -14) :
  (a^2 + b^2 + c^2 = 14) := by

  -- Add all three equations
  have add_all_equations : a^2 + b^2 + c^2 + 6 * a + 2 * b + 4 * c = -14 := by
    calc
      a^2 + b^2 + c^2 + 6 * a + 2 * b + 4 * c = (a^2 + 2 * b) + (b^2 + 4 * c) + (c^2 + 6 * a) := by ring
      _ = 7 + (-7) + (-14) := by rw [h1, h2, h3]
      _ = -14 := by norm_num


  have add_all_squares_eq :  (a + 3)^2 + (b + 1)^2 + (c + 2)^2 = 0 := by
    calc
       (a + 3)^2 + (b + 1)^2 + (c + 2)^2 = (a^2 + 6 * a + 9) + (b^2 + 2 * b + 1) + (c^2 + 4 * c + 4) := by ring
                                      _ = a^2 + b^2 + c^2 + 6 * a + 2 * b + 4 * c + 14 := by ring
                                      _ = -14 + 14 := by rw [add_all_equations]
                                      _ = 0 := by norm_num

  -- Solve for a, b, c
  have eq_a : a + 3 = 0 := by nlinarith [add_all_squares_eq]
  have a_val : a = -3 := by linarith [eq_a]

  have eq_b : b + 1 = 0 := by nlinarith [add_all_squares_eq]
  have b_val : b = -1 := by linarith [eq_b]

  have eq_c : c + 2 = 0 := by nlinarith [add_all_squares_eq]
  have c_val : c = -2 := by linarith [eq_c]

  -- Calculate a^2 + b^2 + c^2
  calc
    a^2 + b^2 + c^2 = (-3)^2 + (-1)^2 + (-2)^2 := by rw [a_val, b_val, c_val]
                  _ = 9 + 1 + 4 := by norm_num
                  _ = 14 := by norm_num