import Mathlib
open Real

/-
51. (Original problem, 1988. 12.13) Let $x, y, z \in \overline{\mathbf{R}^{-}}$, and $x^{2}+y^{2}+z^{2} \leqslant 3$, then
$$27+36 x y z \geqslant 7 \sum x \sum y z$$

Equality holds if and only if $x=y=z=1$.
-/
theorem inequalities_601402 (x y z : ℝ) (hx : x ≤ 0) (hy : y ≤ 0) (hz : z ≤ 0)
    (h : x^2 + y^2 + z^2 ≤ 3) :
    27 + 36 * x * y * z ≥ 7 * (x + y + z) * (y * z + z * x + x * y) ∧
    (27 + 36 * x * y * z = 7 * (x + y + z) * (y * z + z * x + x * y) ↔ x = 1 ∧ y = 1 ∧ z = 1) := by
        constructor
        · -- First, prove the inequality 27 + 36xyz ≥ 7(x+y+z)(yz+zx+xy)
          nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
            sq_nonneg (x + y + z), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
            sq_nonneg (x + 1), sq_nonneg (y + 1), sq_nonneg (z + 1),
            sq_nonneg (x^2 + y^2 + z^2 - 3)]
        · -- Now prove the equality case: 27 + 36xyz = 7(x+y+z)(yz+zx+xy) ↔ x = y = z = 1
          constructor
          · -- Forward direction: if equality holds, then x = y = z = 1
            intro h_eq
            have h1 : x ≤ 0 := hx
            have h2 : y ≤ 0 := hy
            have h3 : z ≤ 0 := hz
            nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
              sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
              sq_nonneg (x + y + z), sq_nonneg (x^2 + y^2 + z^2 - 3)]
          · -- Backward direction: if x = y = z = 1, then equality holds
            rintro ⟨hx1, hy1, hz1⟩
            nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]