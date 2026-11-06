import Mathlib

/- The equation $y = \frac{x + A}{Bx + C}$, where $A,B,$ and $C$ are integers, is shown below. What is $A + B + C$?

[asy]
import graph; size(8.14cm); real lsf=0.5; pen dps=linewidth(0.7)+fontsize(10); defaultpen(dps); pen ds=black; real xmin=-2.52,xmax=5.62,ymin=-4.28,ymax=3.32;

pen cqcqcq=rgb(0.75,0.75,0.75);

/*grid*/ pen gs=linewidth(0.7)+cqcqcq+linetype("2 2"); real gx=1,gy=1;
for(real i=ceil(xmin/gx)*gx;i<=floor(xmax/gx)*gx;i+=gx) draw((i,ymin)--(i,ymax),gs); for(real i=ceil(ymin/gy)*gy;i<=floor(ymax/gy)*gy;i+=gy) draw((xmin,i)--(xmax,i),gs);

Label laxis; laxis.p=fontsize(10);

xaxis("$x$",xmin,xmax,Ticks(laxis,Step=1.0,Size=2,NoZero),Arrows(6),above=true); yaxis("$y$",ymin,ymax,Ticks(laxis,Step=1.0,Size=2,NoZero),Arrows(6),above=true); real f1(real x){return (-x+4)/(x-2);} draw(graph(f1,-2.51,1.99),linewidth(1.2),Arrows(4)); draw(graph(f1,2.01,5.61),linewidth(1.2),Arrows(4));

clip((xmin,ymin)--(xmin,ymax)--(xmax,ymax)--(xmax,ymin)--cycle);

[/asy] -/
theorem algebra_20931 {A B C : ℤ} (h : ∀ x : ℝ, x ≠ -2 → (x + A) / (B * x + C) = (-x + 4) / (x - 2)) (h1 : B * (4 : ℝ) + C ≠ 0) (h2 : (C : ℝ) ≠ 0) (h3 : B * (3 : ℝ) + C ≠ 0) :
    A + B + C = -3 := by
  -- We see that the graph passes through the point $(4,0)$, which gives us the equation \[\frac{4 + A}{4B + C} = 0.\]Therefore, $A = -4$.
  have Amid := h 4 (by linarith)
  field_simp [h1] at Amid
  have Aeq : (A : ℝ) = (-4 : ℤ) := by
    simp only [Int.reduceNeg, Int.cast_neg, Int.cast_ofNat]
    linarith
  apply Int.cast_injective at Aeq
  -- We see that the graph passes through the point $(0,-2)$, which gives us the equation \[\frac{0 - 4}{C} = -2.\]Therefore, $C = 2$.
  have Cmid := h 0 (by linarith)
  field_simp [h2, Aeq] at Cmid
  have Ceq : (C : ℝ) = (2 : ℤ) := by
    rw [← Cmid]
    exact rfl
  apply Int.cast_injective at Ceq
  -- Finally, we see that the graph passes through the point $(3,1)$, which gives us the equation \[\frac{3 - 4}{3B + 2} = 1.\]Solving for $B$, we find $B = -1$.
  have Bmid := h 3 (by linarith)
  field_simp [h3, Aeq] at Bmid
  rw [Ceq] at Bmid
  have Beq : (B : ℝ) = (-1 : ℤ) := by
    ring_nf at Bmid
    simp only [Int.reduceNeg, Int.cast_neg, Int.cast_one]
    linarith
  apply Int.cast_injective at Beq
  rw [Aeq, Beq, Ceq]
  ring
