import Mathlib

/- Many television screens are rectangles that are measured by the length of their diagonals. The ratio of the horizontal length to the height in a standard television screen is $4:3$. What is the horizontal length (in inches) of a ``27-inch'' television screen?

[asy]
fill((0,0)--(8,0)--(8,6)--cycle,gray(0.7));
draw((0,0)--(8,0)--(8,6)--(0,6)--cycle,linewidth(0.7));
draw((0,0)--(8,6),linewidth(0.7));
label("length",(4,0),S);
label("height",(8,3),E);
label("diagonal",(4,3),NW);
[/asy] -/
theorem algebra_15508 {l h d : ℝ} (hl : l > 0) (hh : h > 0)
    (hd : d > 0) (h1 : l / h = 4 / 3) (h2 : l^2 + h^2 = d^2) (h3 : d = 27) :
    l = 21.6 := by
  field_simp at h1
  norm_num
  nlinarith