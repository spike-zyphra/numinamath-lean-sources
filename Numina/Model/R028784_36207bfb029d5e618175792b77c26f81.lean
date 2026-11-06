import Mathlib

/-Let $PQRS$ be a square piece of paper. $P$ is folded onto $R$ and then $Q$ is folded onto $S$. The area of the resulting figure is 9 square inches. Find the perimeter of square $PQRS$. [asy]

/* AMC8 1998 #20P */

size(1inch,1inch);

label("$P$", (0, 72), SE);

label("$Q$", (72, 72), SW);

label("$S$", (0, 0), NE);

label("$R$", (72, 0), NW);

draw((0,0)--(72,0)--(72,72)--(0,72)--cycle);

[/asy]-/
open EuclideanGeometry
open Real

variable {V : Type*} {Point : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Point]
  [NormedAddTorsor V Point]


theorem algebra_20981 {P Q R S : Point} (hsq : dist P Q = dist Q R ∧  dist Q R = dist R S ∧  dist R S = dist S P)
    (h : s = dist P Q ^ 2) (h2 : s * 1 / 4 = 9)(h3: 0 < dist P Q): dist P Q + dist Q R + dist R S + dist S P = 24 := by

  have h1 : s = 36 := by
    linarith
  
  have h4 : dist P Q = 6 := by
    nlinarith [h1, h]

  have h5 : dist P Q = dist Q R := hsq.left
  have h6 : dist Q R = dist R S := hsq.right.left
  have h7 : dist R S = dist S P := hsq.right.right
  
  have h8 : dist Q R = 6 := by
    linarith [h5, h4]

  have h9 : dist R S = 6 := by
    linarith [h6, h8]

  have h10 : dist S P = 6 := by
    linarith [h7, h9]

  linarith [h4, h8, h9, h10]