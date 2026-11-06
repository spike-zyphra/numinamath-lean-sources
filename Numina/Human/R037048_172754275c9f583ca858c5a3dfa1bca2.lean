import Mathlib
import Mathlib.Tactic

/--
The sum of three numbers is 96. The first number is 6 times the third number,
and the third number is 40 less than the second. What is the absolute value of
the difference between the first and second numbers?

(A) 1
(B) 2
(C) 3
(D) 4
(E) 5
-/

theorem algebra_93770 :
  ∃ (x y z : Int),
    x + y + z = 96
    ∧ x = 6 * z
    ∧ z = y - 40
    ∧ Int.natAbs (x - y) = 5 := by
    -- We exhibit a concrete solution: x=42, y=47 and z=7, which verify the four conditions: x + y + z =  -- 96; x = 6 * z; z = y - 40 and |x-y|=5.
  let x := (42 : Int)
  let y := (47 : Int)
  let z := (7  : Int)
  exists x, y, z