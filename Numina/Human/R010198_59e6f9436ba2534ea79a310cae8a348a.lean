import Mathlib

/- On a number line, the coordinates of $P$ and $Q$ are 8 and 48, respectively. The midpoint of $\overline{PQ}$ is $B$, the midpoint of $\overline{BQ}$ is $C$, and the midpoint of $\overline{PC}$ is $D$. What is the coordinate of $D$? -/
theorem algebra_21681 (P Q B C D : ℝ) (hP : P = 8) (hQ : Q = 48)
    (hB : B = (P + Q) / 2) (hC : C = (B + Q) / 2) (hD : D = (P + C) / 2) :
    D = 23 := by
  linarith