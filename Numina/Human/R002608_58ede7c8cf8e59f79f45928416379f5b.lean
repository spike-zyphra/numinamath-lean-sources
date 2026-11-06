import Mathlib

/- Doug and Dave shared a pizza with 8 equally-sized slices. Doug wanted a plain pizza, but Dave wanted anchovies on half the pizza. The cost of a plain pizza was 8 dollars, and there was an additional cost of 2 dollars for putting anchovies on one half. Dave ate all the slices of anchovy pizza and one plain slice. Doug ate the remainder. Each paid for what he had eaten. How many more dollars did Dave pay than Doug?
(A) 1(B) 2(C) 3(D) 4(E) 5 -/
theorem algebra_96271 {d d' : ℝ} (hd : d = 8) (hd' : d' = 2) :
(d / 2 + d'+ 1 / 4 * d / 2) - ((1 - 1 / 4) * d / 2 ) = 4 := by
    --substitute the values of the costs of plain pizza and anchovies
    rw[hd,hd']
    --solve the calculation
    field_simp
    ring_nf