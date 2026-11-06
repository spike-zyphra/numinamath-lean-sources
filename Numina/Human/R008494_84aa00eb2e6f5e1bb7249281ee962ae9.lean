import Mathlib
open Mathlib
/--
Bricklayer Brenda would take $9$ hours to build a chimney alone, and bricklayer Brandon would take $10$ hours to build it alone. When they work together they talk a lot, and their combined output is decreased by $10$ bricks per hour. Working together, they build the chimney in $5$ hours. How many bricks are in the chimney?
$\textbf{(A)}\ 500 \qquad \textbf{(B)}\ 900 \qquad \textbf{(C)}\ 950 \qquad \textbf{(D)}\ 1000 \qquad \textbf{(E)}\ 1900$
-/
lemma algebra_1194 (bricks brenda_alone brandon_alone : ℚ) (h1 : bricks = 9 * brenda_alone) (h2 : bricks = 10 * brandon_alone) (h3 : bricks = 5 * (brenda_alone + brandon_alone - 10)) : bricks = 900 := by
  -- Let $h$ be the number of bricks in the chimney. 
  -- Without talking, Brenda and Brandon lay $\frac{h}{9}$ and $\frac{h}{10}$ bricks per hour respectively,
  have s1 : brenda_alone = ((1 : ℚ) / 9) * bricks := by linarith
  have s2 : brandon_alone = ((1 : ℚ) / 10) * bricks := by linarith
  -- so together they lay $\frac{h}{9}+\frac{h}{10}-10$ per hour together. 
  have s3 : bricks = 5 * (((1 : ℚ) / 9) * bricks + ((1 : ℚ) / 10) * bricks - 10) := by linarith
  -- Since they finish the chimney in $5$ hours, $h=5\left( \frac{h}{9}+\frac{h}{10}-10 \right)$. Thus, $h=900 \Rightarrow B$.
  linarith