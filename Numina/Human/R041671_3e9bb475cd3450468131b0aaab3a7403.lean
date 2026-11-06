import Mathlib

open Real

/- 6・97 Let $x, y, z$ be positive numbers, and $x^{2}+y^{2}+z^{2}=1$, try to find the minimum value of the following expression

$$

S=\frac{x y}{z}+\frac{y z}{x}+\frac{z x}{y} .

$$
 -/
theorem inequalities_220275 :
    IsLeast {(x * y / z + y * z / x + z * x / y) | (x : ℝ) (y: ℝ) (z: ℝ) (_: 0 < x) (_: 0 < y) (_: 0 < z) (_: x^2 + y^2 + z^2 = 1)} (√3) := by
  -- prove an auxilarity lemma that x^2 * y^2 / z^2 + y^2 * z^2 / x^2 ≥ 2 * y^2 in 2 vairable am-gm style
  have aux {x y z : ℝ} (hx : x > 0) (hy: y > 0) (hz: z > 0) :
    x^2 * y^2 / z^2 + y^2 * z^2 / x^2 ≥ 2 * y^2 := by
    have : (x*y/z - y*z/x)^2 ≥ 0 := by positivity
    convert_to x^2 * y^2 / z^2 + y^2 * z^2 / x^2 - 2 * y^2 ≥ 0 at this
    . ring_nf
      field_simp
      ring
    linarith
  constructor
    -- √3 is a limit by plugging in 1/√3, 1/√3, 1/√3
  . use 1/√3, 1/√3, 1/√3
    use by positivity, by positivity, by positivity
    simp [-one_div]
    norm_num
    ring_nf
    nth_rw 2 [(show 3 = √3 * √3 by simp)]
    simp [-mul_self_sqrt]
    -- for any t in the set, we'll prove 3 ≤ t^2
  . rintro t ⟨x, y, z, hx, hy, hz, hxyz, ht⟩
    rw [← @sqrt_sq t]
    swap; rw [← ht]; positivity
    gcongr
    -- write 3 as 3 * (x^2 + y^2 + z^2) = x^2*y^2/z^2 + y^2*z^2/x^2 + z^2*x^2/y^2 + 2 * (x^2 + y^2 + z^2)
    -- use the lemma 3 times to prove the inequality. the rhs is t^2
    calc
      3 = 3 * (x^2 + y^2 + z^2) := by rw [hxyz]; simp
      _ ≤ x^2*y^2/z^2 + y^2*z^2/x^2 + z^2*x^2/y^2 + 2 * (x^2 + y^2 + z^2) :=
        by linarith [aux hx hy hz, aux hy hz hx, aux hz hx hy]
      _ = t^2 := by
        rw [← ht]
        ring_nf
        field_simp
        ring