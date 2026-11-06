import Mathlib

theorem algebra_237092 {x y z : ℝ} (h1 : 4*x^2-2*x-30*y*z=25*y^2+5*y+12*x*z) (h2 : 25*y^2+5*y+12*x*z=9*z^2-3*z-20*x*y) :
    (2*x+5*y=0 ∧ 3*z+5*y=0 ∧ 3*z-2*x=0) ∨ (2*x+5*y=0 ∧ 3*z+5*y=1 ∧ 3*z-2*x=1) ∨ (2*x+5*y=1 ∧ 3*z+5*y=0 ∧ 3*z-2*x=-1) ∨ (2*x+5*y=-1 ∧ 3*z+5*y=-1 ∧ 3*z-2*x=0) := by
  have eq1 : (2 * x + 5 * y) * (2 * x - 5 * y - 1 - 6 * z) = 0 := by
    nlinarith
  cases' (mul_eq_zero.1 eq1) with h3 h4
  · -- Case where 2x + 5y = 0
    have ha : 2 * x + 5 * y = 0 := by
      linarith
    have h2' : (3 * z + 5 * y) * (3 * z + 5 * y - 1) = 0 := by
      have h5 : x = -5 * y / 2 := by
        linarith
      rw [h5] at h1 h2
      nlinarith
    cases (mul_eq_zero.1 h2') with
    | inl h4 =>
      have h5 : 3 * z + 5 * y = 0 := by linarith
      have h6 : 3 * z - 2 * x = 0 := by
        have h5' : x = -5 * y / 2 := by
          linarith
        rw [h5'] 
        linarith 
      left 
      constructor 
      · exact ha
      constructor 
      · exact h5
      · exact h6
    | inr h5 =>
      have h5 : 3 * z + 5 * y = 1 := by linarith
      have h6 : 3 * z - 2 * x = 1 := by
        have h5' : x = -5 * y / 2 := by
          linarith
        rw [h5'] 
        linarith 
      right
      left
      constructor
      · exact ha
      constructor
      · exact h5
      · exact h6
  · -- Case where 2x - 5y - 1 - 6z = 0
    have eq2 : 2 * x - 5 * y - 1 - 6 * z = 0 := by
      linarith
    have h5 : (2 * x + 5 * y - 1) * (2 * x + 5 * y + 1) = 0 := by
      nlinarith [sq_nonneg (2 * x + 5 * y), sq_nonneg (3 * z - 2 * x - 1), sq_nonneg (3 * z + 5 * y - 1), sq_nonneg (x + 2 * y), sq_nonneg (z - y), sq_nonneg (z), sq_nonneg (x), sq_nonneg (y), sq_nonneg (z - 1)]
    cases (mul_eq_zero.1 h5) with
    | inl h6 =>
      have h7 : 2 * x + 5 * y = 1 := by linarith
      have h8 : 3 * z + 5 * y = 0 := by
        nlinarith [sq_nonneg (z - 1), sq_nonneg (x - 0), sq_nonneg (y - 0), sq_nonneg (z - 1), sq_nonneg (x - 0), sq_nonneg (y - 0)]
      have h9 : 3 * z - 2 * x = -1 := by
        nlinarith 
      right
      right
      left
      constructor
      · exact h7
      constructor
      · exact h8
      · exact h9
    | inr h7 =>
      have h7 : 2 * x + 5 * y = -1 := by linarith
      have h8 : 3 * z + 5 * y = -1 := by
        nlinarith [sq_nonneg (z - 1), sq_nonneg (x - 0), sq_nonneg (y - 0), sq_nonneg (z - 1), sq_nonneg (x - 0), sq_nonneg (y - 0)]
      have h9 : 3 * z - 2 * x = 0 := by
        nlinarith
      right
      right
      right
      constructor
      · exact h7
      constructor
      · exact h8
      · exact h9