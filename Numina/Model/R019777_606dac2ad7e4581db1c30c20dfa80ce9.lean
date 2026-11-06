import Mathlib

theorem algebra_249712 (x y : ℝ) (hx : x < y) (hy : y < 0) :
    |y| < Real.sqrt (x * y) ∧ Real.sqrt (x * y) < |x + y| / 2 ∧ |x + y| / 2 < |x| := by
  have h1 : x < 0 := by linarith
  have h2 : x + y < 0 := by linarith
  have h3 : |y| = -y := by
    rw [abs_of_neg hy]
  have h4 : |x| = -x := by
    rw [abs_of_neg (show x < 0 by linarith)]
  have h5 : |x + y| = -(x + y) := by
    rw [abs_of_neg (show x + y < 0 by linarith)]
  -- prove $|y| < \sqrt{xy}$
  have h7 : x * y > 0 := by nlinarith
  have h8 : |y| < Real.sqrt (x * y) := by
    rw [h3]
    have h9 : Real.sqrt (x * y) > 0 := by positivity
    have h10 : (-y) < Real.sqrt (x * y) := by
      nlinarith [Real.sqrt_nonneg (x * y),
        Real.sq_sqrt (show 0 ≤ x * y by nlinarith),
        sq_nonneg (Real.sqrt (x * y) + y),
        sq_nonneg (x - y),
        mul_pos (show 0 < -y by nlinarith) (show 0 < -x by nlinarith)
      ]
    linarith
  -- prove $\sqrt{xy} < \frac{|x+y|}{2}$
  have h11 : Real.sqrt (x * y) < |x + y| / 2 := by
    rw [h5]
    have h12 : Real.sqrt (x * y) > 0 := by positivity
    have h14 : Real.sqrt (x * y) < (- (x + y) / 2) := by
      nlinarith [Real.sqrt_nonneg (x * y),
        Real.sq_sqrt (show 0 ≤ x * y by nlinarith),
        sq_nonneg (Real.sqrt (x * y) - (- (x + y) / 2)),
        sq_pos_of_pos (show 0 < - (x + y) / 2 by nlinarith),
        sq_nonneg (x - y),
        mul_pos (show 0 < -x by nlinarith) (show 0 < -y by nlinarith)
      ]
    linarith
  -- prove $\frac{|x+y|}{2} < |x|$
  have h15 : |x + y| / 2 < |x| := by
    rw [h5, h4]
    nlinarith
  constructor
  · exact h8
  constructor
  · exact h11
  · exact h15