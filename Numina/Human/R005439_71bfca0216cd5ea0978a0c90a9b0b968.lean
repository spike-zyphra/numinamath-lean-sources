import Mathlib

/-!
Let $ABC$ be a triangle with $\angle BAC = 90^\circ$, $AB = AC = 6$.
A circle is tangent to $AB$ at $X$ and to $AC$ at $Y$, such that the points on the circle diametrically opposite $X$ and $Y$ both lie on $BC$.
Let $S$ be the area of the portion of the circle lying outside the triangle.
Prove: $S = \pi - 2$.
-/

open Real

theorem geometry_608299 :
  (1/4 : ℝ) * π * 2^2 - (1/2 : ℝ) * 2^2 = π - 2 :=
by
  calc
    (1/4 : ℝ) * π * 2^2 - (1/2 : ℝ) * 2^2
      = (1/4 : ℝ) * π * 4 - (1/2 : ℝ) * 4 := by norm_num
  _ = π - 2 := by ring