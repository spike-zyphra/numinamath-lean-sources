import Mathlib

/- The circular region of the sign (below, left) has an area of 154 square inches. Vanessa would like to place a tiny ribbon (shaded) around the circle's edge. To be sure she has enough ribbon, she decides to buy 2 inches more of the ribbon than the original circle's circumference. How many inches of ribbon will Vanessa need to buy if she estimates $\pi = \frac{22}{7}$?
[asy]import graph;
size(125,72.5);
picture p;
draw(p,unitsquare);
filldraw(p,Circle((.5,.5),.3),white);
label(p,"Enter",(.5,.5),ZapfChancery("m","n"));
add(p);
filldraw(Circle((2,.5),.4),gray(.6));
add(shift(1.5*right)*p);
draw((1.1,.5)--(1.4,.5),EndArrow(5,25));[/asy]-/

theorem algebra_11669 {r : ℝ} (hr : r > 0) (h : r^2 * (22 / 7) = 154) :

    2 * (22 / 7 ) * r + 2 = 46 := by
    --Say the radius of the circle is $r$. Then the area of the circle is $\pi r^2,$ which we estimate to $154=\frac{22}{7}r^2$. If we multiply both sides by $\frac{7}{22}$, we get $r^2=49$ or $r=7$. The circle's circumference is $2\pi r$, which we again estimate to $\frac{44}{7}r=44$. Vanessa wants two extra inches of ribbon, so she needs to buy $44+2=\boxed{46}$ inches of ribbon.
    have e := congrArg (fun t  => t * (7 / 22)) h; ring_nf at e
    rw [show (49 : ℝ) = 7 ^ 2 by ring_nf] at e
    rw [sq_eq_sq_iff_eq_or_eq_neg] at e
    cases e with
    | inl h2 =>
      rw [h2]
      ring_nf
    | inr h2 =>
      linarith