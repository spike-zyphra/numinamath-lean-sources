import Mathlib

open Real Set
open scoped BigOperators

/- 2. Given $x, y, z \geqslant 1$, find the minimum value of the expression


$$

A=\frac{\sqrt{3 x^{4}+y}+\sqrt{3 y^{4}+z}+\sqrt{3 z^{4}+x}-3}{x y+y z+z x}

$$
 -/
theorem algebra_223892 :
  IsLeast {a : ℝ | ∃ x y z : ℝ, x ≥ 1 ∧ y ≥ 1 ∧ z ≥ 1 ∧
    a = (sqrt (3 * x^4 + y) + sqrt (3 * y^4 + z) + sqrt (3 * z^4 + x) - 3) /
    (x * y + y * z + z * x)} 1 := by
  constructor
    -- first show x = y = z = 1 proves 1 is a possible value
  . use 1, 1, 1
    norm_num
    rw [show (4:ℝ) = 2^2 by norm_num]
    simp; norm_num
    -- next we'll show 1 is a lower bound
  . rintro a ⟨x, y, z, hx, hy, hz, ha⟩
    -- first prove lemma that p^2 ≤ √(3p^4 + q) - 1 for p, q matching the provided hypothesis
    have aux₁ {p q} (hp: 1 ≤ p) (hq: 1 ≤ q) : p^2 ≤ √(3*p^4 + q) - 1 := by calc
      -- mainly rewrite 3p^4 + q ≥ p^4 + 2p^2 + 1
      p^2 = √((p^2+1)^2) - 1 := by rw [sqrt_sq (by positivity)]; ring
      _ = √(p^4 + 2*p^2+ 1) - 1 := by ring_nf
      _ ≤ √(p^4 + 2*p^4 + q) - 1 := by
        gcongr <;> linarith
      _ = √(3*p^4 + q) - 1 := by ring_nf
    -- next prove lemma that xy + yz + zx ≤ x^2 + y^2 + z^2
    have aux₂ {p q r : ℝ} : p*q + q*r + r*p ≤ p^2 + q^2 + r^2 := by
      have : 0 ≤ (p-q)^2 + (q-r)^2 + (r-p)^2 := by positivity
      linear_combination this/2
    rw [ha]
    -- now using last two lemma prove the target, first show 1 ≤ (x^2 + y^2 + z^2)/(x*y+y*z+z*x)  by previous lemma then use first lemma
    calc
      1 = (x*y+y*z+z*x)/(x*y+y*z+z*x) := by field_simp
      _ ≤ (x^2 + y^2 + z^2)/(x*y+y*z+z*x) := by
        gcongr ?_ / _
        exact aux₂
      _ ≤ ((√(3*x^4 + y) - 1) + (√(3*y^4 + z) - 1) + (√(3*z^4 + x) - 1))/ (x*y+y*z+z*x) := by
        gcongr <;> exact aux₁ (by assumption) (by assumption)
      _ = _ := by ring_nf