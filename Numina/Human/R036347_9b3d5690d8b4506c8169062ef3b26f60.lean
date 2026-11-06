import Mathlib

/- 4・107 Assume $x, y, z$ are all real numbers, and it is known that they satisfy\n$$\\left\\{\\begin{array}{l}\nx+y+z=a \\\\\nx^{2}+y^{2}+z^{2}=\\frac{a^{2}}{2}(a>0) .\n\\end{array}\\right.$$\n\nProve that $x, y, z$ cannot be negative, and they cannot be greater than $\\frac{2}{3} a$. -/
theorem algebra_601947 (x y z a : ℝ) (ha : 0 < a)
    (h1 : x + y + z = a) (h2 : x^2 + y^2 + z^2 = a^2 / 2) :
    ¬x < 0 ∧ ¬y < 0 ∧ ¬z < 0 ∧ ¬x > 2 * a / 3 ∧ ¬y > 2 * a / 3 ∧ ¬z > 2 * a / 3 := by
  suffices H {x y z : ℝ} (h1 : x + y + z = a) (h2 : x^2 + y^2 + z^2 = a^2 / 2) : ¬x < 0 ∧ ¬x > 2 * a / 3
  . obtain ⟨hx1, hx2⟩ := H h1 h2
    obtain ⟨hy1, hy2⟩ := H (show y + z + x = a by linarith only [h1]) (show y^2 + z^2 + x^2 = a^2 / 2 by linarith only [h2])
    obtain ⟨hz1, hz2⟩ := H (show z + x + y = a by linarith only [h1]) (show z^2 + x^2 + y^2 = a^2 / 2 by linarith only [h2])
    exact ⟨hx1, hy1, hz1, hx2, hy2, hz2⟩
  replace h1 : z = a - x - y := by linarith only [h1]
  rw [h1] at h2
  replace h2 : (y + (x - a) / 2) ^ 2 = x * (2 * a - 3 * x) / 4 := by linarith only [h2]
  replace h2 : x * (2 * a - 3 * x) / 4 ≥ 0 := by
    rw [← h2]
    exact sq_nonneg _
  constructor <;> nlinarith only [h2, ha]
