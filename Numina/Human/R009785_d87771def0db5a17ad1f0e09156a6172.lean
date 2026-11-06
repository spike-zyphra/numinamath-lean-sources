import Mathlib

/- Given vectors $\overrightarrow{a}=(3,x^{2}+2,3)$ and $\overrightarrow{b}=(x-4,2,x)$, if $\overrightarrow{a} \perp \overrightarrow{b}$, then the value of the real number $x$ is ______. -/
theorem algebra_9148 (x : ℝ) (a b : ℝ × ℝ × ℝ)
    (ha : a = (3, x ^ 2 + 2, 3)) (hb : b = (x - 4, 2, x)) :
    a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2 = 0 ↔
    x = -4 ∨ x = 1 := by
  -- Expand the definition and it reduces to a quadratic equation
  simp [ha, hb]
  constructor <;> intro h
  . by_contra!
    nlinarith (config := {splitNe := true})
  . cases h <;> nlinarith
