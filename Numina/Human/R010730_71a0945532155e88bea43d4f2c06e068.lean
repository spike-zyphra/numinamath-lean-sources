import Mathlib

open Real

/- The larger circle has center $O$ and passes through $D$. The smaller circle has diameter $OD$. What percent of the larger circle's area is gray?

[asy]import graph;
draw(Circle((0,0),30),black);
fill(Circle((0,-15),15),gray(.6));
draw(Circle((0,-15),15),black);
draw((0,0)--(0,-30),black);
label("O",(0,0),N);
label("D",(0,-30),S);
[/asy] -/
theorem algebra_20261 (r R : ℝ) (hr : r > 0) (hR : R > 0)
    (hR1 : R = r / 2) :
    (π * R ^ 2) / (π * r ^ 2) = 25 / 100 := by
  rw [hR1]
  ring_nf
  calc
    _ = π * π⁻¹ * (r * r⁻¹) ^ 2 * (1 / 4) := by
      ring_nf
    _ = _ := by
      rw [mul_inv_cancel₀ Real.pi_ne_zero, mul_inv_cancel₀ (by linarith)]
      norm_num