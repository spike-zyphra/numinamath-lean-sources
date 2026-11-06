import Mathlib
open Real Set

/- The volume of the solid of revolution obtained by rotating the figure enclosed by the curves ${{x}^{2}}=-4y$, ${{x}^{2}}=4y$, $x=-4$, and $x=4$ around the $y$-axis is ${{V}_{1}}$. The volume of the solid of revolution obtained by rotating the figure composed of points $\left( x,y \right)$ that satisfy ${{x}^{2}}+{{y}^{2}}\leqslant 16$, ${{x}^{2}}+{{\left( y-2 \right)}^{2}}\geqslant 4$, and ${{x}^{2}}+{{\left( y+2 \right)}^{2}}\geqslant 4$ around the $y$-axis is ${{V}_{2}}$. Then (   ).
A: ${{V}_{1}}=\frac{1}{2}{{V}_{2}}$
B: ${{V}_{1}}=\frac{2}{3}{{V}_{2}}$
C: ${{V}_{1}}={{V}_{2}}$
D: ${{V}_{1}}=2{{V}_{2}}$-/

theorem calculus_9959 {V1 V2 : ℝ}
    (hV1 : V1 = ∫ x in (-4)..4, π * (-x^2 - 4) ^ 2)
    (hV2 : V2 = ∫ x in (-4)..4, π * (x^2 + 4) ^ 2) :
    V1 = V2 := by
  -- Expand the definitions of V1 and V2
  rw [hV1, hV2]
  --  Prove that the two integrals are equal by demonstrating
  congr
  --integrand functions are equal at each value of x,
  ext x
  -- expand and prove using algebraic operations
  calc
    π * (-x^2 - 4) ^ 2 = π * (x^4 + 8*x^2 + 16) := by ring
    _ = π * (x^2 + 4) ^ 2 := by ring

