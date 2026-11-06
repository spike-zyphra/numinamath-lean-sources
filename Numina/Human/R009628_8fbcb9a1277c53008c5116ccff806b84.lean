import Mathlib

/- Two circles have the same center $C.$ (Circles which have the same center are called concentric.) The larger circle has radius $10$ and the smaller circle has radius $6.$ Determine the area of the ring between these two circles. [asy]
import graph;
filldraw(circle((0,0),10), lightgray, black+linewidth(1));
filldraw(circle((0,0),6), white, black+linewidth(1));
dot((0,0));
label("$C$",(0,0),NE);
[/asy] -/
theorem algebra_16804 {R r : ℝ} (hR : R = 10) (hr : r = 6) :
    Real.pi * (R^2 - r^2) = 64 * Real.pi := by
  subst_vars; linarith [Real.pi_pos]