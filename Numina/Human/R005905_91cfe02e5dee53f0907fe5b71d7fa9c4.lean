import Mathlib

/-
 Let $A B C D$ be a rectangle with $A B=20$ and $A D=23$. Let $M$ be the midpoint of $C D$,
 and let $X$ be the reflection of $M$ across point $A$. Compute the area of triangle $X B D$.
 -/

theorem geometry_610638 (A B C D M X : ℝ × ℝ)
    (h0 : A = (0, 23)) (h1 : B = (20, 23)) (h2 : C = (20, 0))
    (h3 : D = (0, 0)) (h4 : M = ((C.1 + D.1) / 2, (C.2 + D.2) / 2))
    (h5 : X = (2 * A.1 - M.1, 2 * A.2 - M.2)) :
    1 / 2 * |X.1 * B.2 + B.1 * D.2 + D.1 * X.2 - (X.2 * B.1 + B.2 * D.1 + D.2 * X.1)| = 575 := by

    simp [h0, h1, h2, h3, h4, h5]
    norm_num