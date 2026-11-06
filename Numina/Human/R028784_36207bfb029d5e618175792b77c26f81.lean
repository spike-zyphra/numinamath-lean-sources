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
    rcases hsq with ⟨hP,⟨hQ,hR⟩⟩
    --After folding the square twice the resulting figure is isosceles triangle with area 9 square inches. Since there are 4 such congruent triangles in the square, the area of the square is 36 square inches. Therefore, the sides of $PQRS$ are 6 inches, and the perimeter is $\boxed{24}$ inches.
    have e := congrArg ( fun (n) => ((n) * 4)) h2; simp at e; ring_nf at e
    rw [e] at h
    rw [show (36 : ℝ) = 6 ^ 2 by ring_nf] at h
    rw [sq_eq_sq] at h
    rw[← hR]; rw [← hQ]; rw [← hP]; rw [← h]
    ring_nf
    linarith
    linarith
