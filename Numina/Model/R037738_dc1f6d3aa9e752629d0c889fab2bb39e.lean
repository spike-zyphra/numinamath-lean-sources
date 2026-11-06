import Mathlib

theorem algebra_67846 :
  let A : ℚ := 1/15;
  let B : ℚ := (3/2) * A;
  let C : ℚ := 2 * A;
  let t1 : ℚ := 3/2;
  let work1 : ℚ := A * t1;
  let t2 : ℚ := ((1/2) - work1) / (A + B);
  let t3 : ℚ := (1/2) / (A + B + C);
  (t1 + t2 + t3) * 60 = 334 := by 
  norm_num