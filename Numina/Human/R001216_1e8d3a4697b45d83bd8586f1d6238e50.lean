import Mathlib

/- Triangle $ABC$ is an isosceles right triangle with a right angle at $A$. Segments $BD$ and $BE$ trisect angle $ABC$. What is the degree measure of angle $BDE$?

[asy]draw((0,0)--(-1,0)--(-1,1)--(0,0)--cycle,linewidth(2));
draw((0,0)--dir(165)*1/cos(pi/12),linewidth(2));
draw((0,0)--dir(150)*1/cos(pi/6),linewidth(2));
draw((-1,.07)--(-.93,.07)--(-.93,0),linewidth(1));

label("A",(-1,0),SW);
label("B",(0,0),SE);
label("C",(-1,1),NW);
label("D",dir(150)*1/cos(pi/6),W);
label("E",dir(165)*1/cos(pi/12),W);
[/asy] -/
theorem algebra_21562 {A B C ABE EBD DBC : ℝ} (hABC : A + B + C = 180 ∧ A = 90 ∧ B = C) (h1 : ABE = EBD) (h2 : EBD = DBC) (h3 : ABE + EBD + DBC = B) : 180 - A - ABE - EBD = 60 := by
  linarith