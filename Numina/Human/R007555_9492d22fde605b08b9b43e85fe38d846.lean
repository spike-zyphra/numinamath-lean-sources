import Mathlib

/-Determine $3x_4+2x_5$ if $x_1$, $x_2$, $x_3$, $x_4$, and $x_5$ satisfy the system of equations below.

$2x_1+x_2+x_3+x_4+x_5=6$
$x_1+2x_2+x_3+x_4+x_5=12$
$x_1+x_2+2x_3+x_4+x_5=24$
$x_1+x_2+x_3+2x_4+x_5=48$
$x_1+x_2+x_3+x_4+2x_5=96$-/

theorem Algebra_696 (x1 x2 x3 x4 x5 : ℝ) (h1 : 2*x1+x2+x3+x4+x5=6) (h2 : x1+2*x2+x3+x4+x5=12) (h3 : x1+x2+2*x3+x4+x5=24) (h4 : x1+x2+x3+2*x4+x5=48) (h5 : x1+x2+x3+x4+2*x5=96) : 3*x4+2*x5 = 181 := by
--Adding all five [equations](https://artofproblemsolving.com/wiki/index.php/Equation) gives us $6(x_1 + x_2 + x_3 + x_4 + x_5) = 6(1 + 2 + 4 + 8 + 16)$ so $x_1 + x_2 + x_3 + x_4 + x_5 = 31$. 
have H1 : 6 + 12 + 24 + 48 + 96 = (186 : ℝ) := by ring 
nth_rewrite 1 [←h1, ←h2, ←h3, ←h4, ←h5] at H1
ring_nf at H1
have Hfactor : (186 : ℝ)  = 31*6 := by ring
rw [Hfactor] at H1
simp [←add_mul] at H1
--Subtracting this from the fourth given equation gives $x_4 = 17$
have H2 : 48 - 31 = (17 : ℝ) := by ring
rw [←h4, ←H1] at H2
ring_nf at H2
--and subtracting it from the fifth given equation gives $x_5 = 65$
have H3 : 96 - 31 = (65 : ℝ) := by ring
rw [←h5, ←H1] at H3
ring_nf at H3
--so our answer is $3\cdot17 + 2\cdot65 = \boxed{181}$
rw [H2, H3]
ring_nf