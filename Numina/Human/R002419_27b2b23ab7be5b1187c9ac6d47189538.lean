import Mathlib
import Mathlib.Tactic.NormNum

/--
Alicia had two containers. The first was 5/6 full of water, and the second was empty.
She poured all the water from the first container into the second container, at which
point the second container was 3/4 full of water. What is the ratio of the volume of
the first container to the volume of the second container?

(A) 5/8
(B) 4/5
(C) 7/8
(D) 9/10
(E) 11/12
-/
theorem algebra_93113 {x y : ℝ} (hy : y ≠ 0)
    (h1 : x * 5 / 6 = y * 3 / 4) :
  x / y = 9 / 10 := by
    -- We know that `x*(5/6) = y*(3/4)`. We'll show `x / y = (3/4)/(5/6) = 9/10`.
  calc
    x / y
      = (x * 5/6) / (y * (5/6)) := by
    -- We factored out (5/6) from numerator and denominator.
        ring
    _ = (y * 3/4) / (y * (5/6)) := by rw [h1] 
    _ = 3/4 / (5/6) := by
    -- We canceled out y, which is nonzero by hypothesis hy.
      field_simp [hy]
      ring
    _ = 9 / 10 := by
    -- At this point without variables, we just operate arithmetically.
      ring