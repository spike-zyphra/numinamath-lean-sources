import Mathlib

/- Abe can paint the room in 15 hours, Bea can paint 50 percent faster than Abe, and Coe can paint twice as fast as Abe. Abe begins to paint the room and works alone for the first hour and a half. Then Bea joins Abe, and they work together until half the room is painted. Then Coe joins Abe and Bea, and they work together until the entire room is painted. Find the number of minutes after Abe begins for the three of them to finish painting the room. -/
theorem algebra_67846 :
  let A : ℚ := 1/15;
  let B : ℚ := (3/2) * A;
  let C : ℚ := 2 * A;
  let t1 : ℚ := 3/2;
  let work1 : ℚ := A * t1;
  let t2 : ℚ := ((1/2) - work1) / (A + B);
  let t3 : ℚ := (1/2) / (A + B + C);
  (t1 + t2 + t3) * 60 = 334 := by
  -- The total amount of time they take is\[90+\frac{12}{5}\times 60+\frac{5}{3}\times 60 = 90+ 144 + 100 = \boxed{334} \text{\ minutes.}\]
  norm_num