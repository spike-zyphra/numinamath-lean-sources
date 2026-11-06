import Mathlib

/- The harmonic mean of two numbers can be calculated as twice their product divided by their sum. The harmonic mean of 11 and 20162016 is closest to which integer?
(A) 2(B) 45(C) 504(D) 1008(E) 2015 -/
theorem algebra_97311 (m : ℝ) (hm: m = (2 * 1 * 2016 / (1 + 2016 : ℝ))):
  |2 - m| < |45 - m| ∧ |2 - m| < |504 - m| ∧ |2 - m| < |1008 - m| ∧ |2 - m| < |2015 - m|
 := by
  -- first plug in the harmonic mean into goal and normalize to get |2 / 2017| < |86733 / 2017| ∧ |2 / 2017| < |1012536 / 2017| ∧ |2 / 2017| < |2029104 / 2017| ∧ |2 / 2017| < |4060223 / 2017|
  rw [hm]
  norm_num
  have : |(2:ℝ)/2017| = (2:ℝ)/2017 := by norm_num
  rw [this]
  -- now extract the 4 inequalities from goal and for each, first determine the absolute value terms and then just normalize the values
  constructor
  . have : |(86733:ℝ)/2017| = (86733 :ℝ)/2017 := by norm_num
    rw [this]
    norm_num
  constructor
  . have : |(1012536 :ℝ)/2017| = (1012536  :ℝ)/2017 := by norm_num
    rw [this]
    norm_num
  constructor
  . have : |(2029104 :ℝ)/2017| = (2029104 :ℝ)/2017 := by norm_num
    rw [this]
    norm_num
  . have : |(4060223 :ℝ)/2017| = (4060223 :ℝ)/2017 := by norm_num
    rw [this]
    norm_num