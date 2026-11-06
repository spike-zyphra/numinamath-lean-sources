import Mathlib

/- Given real numbers $x$, $y$, and $z$ that satisfy $x + y + z = 2$, find the minimum value of $2x^{2} + 3y^{2} + z^{2}$. -/
theorem algebra_9386: IsLeast { s:ℝ | ∃(x y z:ℝ), (s = 2*x^2+3*y^2+z^2 ∧  x+y+z=(2:ℝ))} ((24:ℝ) / 11) := by
rw [IsLeast, lowerBounds]
simp
constructor
-- for the left conjunction, we prove 2x^2+3y^2+z^2 can be 24/11. later we will use a Cauchy-Schwarz-like inequality to do proofs, and that indicates when √2/√3 x=√3/√2 y; √3y = z/√3; √2 x=z/√2, the minimum value is taken. combine with x+y+z=2, we can solve x=6/11, y=4/11,z=12/11. so use these values to verify.
use (6/11)
use (4/11)
use (12/11)
ring_nf
tauto
-- here comes the right conjunction. It's a kind of Cauchy-Schwarz inequality of 3-dimension. (a^2x^2+b^2y^2+c^2z^2) ≤ (x^2+y^2+z^2)(a^2+b^2+c^2).
-- The key is find forms like "2ab ≤ a^2+b^2", so here we directly find these forms, instead of dealing with lemmas of Cauchy-Schwarz inequality.
intro s x y z hs h
rw [hs]
have eq1: (2 * x ^ 2 + 3 * y ^ 2 + z ^ 2)*(1/2 + 1/3 + 1) - (x+y+z)^2 = (2/3 * x^2 + 3/2 * y^2 - 2*x*y) + (2*x^2+z^2/2-2*x*z)+(3*y^2+z^2/3-2*y*z) := by ring
-- there are three pairs of the form "a^2+b^2-2ab", which must ≥ 0.
have h1: (2/3 * x^2 + 3/2 * y^2 - 2*x*y) = (√2/√3 * x - √3/√2 *y)^2 := by
  ring_nf; simp; ring
have h2: (2*x^2+z^2/2-2*x*z) = (√2*x-z/√2)^2 := by
  ring_nf; simp
have h3: (3*y^2+z^2/3-2*y*z) = (√3*y-z/√3)^2 := by
  ring_nf; simp
rw [h1, h2, h3] at eq1
-- substitute back
have ineq: (2 * x ^ 2 + 3 * y ^ 2 + z ^ 2)*(11/6) ≥ 4 := by
  have ht1: (11/6 :ℝ) = (1/2 + 1/3 + 1) := by ring
  have ht2: (x+y+z)^2 = 4 := by
    rw [h]; norm_num
  rw [ht1, ← ht2]
  have ht3: 0 ≤ (2 * x ^ 2 + 3 * y ^ 2 + z ^ 2)*(1/2 + 1/3 + 1) - (x+y+z)^2 := by
    rw [eq1]
    have h11: 0 ≤ (√2/√3 * x - √3/√2 *y)^2 := sq_nonneg (√2/√3 * x - √3/√2 *y)
    have h22: 0 ≤ (√2*x-z/√2)^2 := sq_nonneg (√2*x-z/√2)
    have h33: 0 ≤ (√3*y-z/√3)^2 := sq_nonneg (√3*y-z/√3)
    linarith [h11,h22,h33]
  exact sub_nonneg.mp ht3
have ht4: (24/11: ℝ) = 4 / (11/6) := by ring
rw [ht4]
have ht5: 0 < (11/6:ℝ) := by norm_num
exact (div_le_iff₀ ht5).mpr ineq