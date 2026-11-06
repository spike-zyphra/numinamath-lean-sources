import Mathlib
open Real

/- 4.6.13 ** Given the sides of a triangle are $a, b, c$, and the area is $S$. Prove:

$$
a^{2}+b^{2}+c^{2} \geqslant 4 \sqrt{3} S,
$$

and specify the condition for equality. -/
theorem inequalities_284761 (a b c s : ℝ)
  (hpos : a > 0 ∧ b > 0 ∧ c > 0)
  (htri : a + b > c ∧ a + c > b ∧ b + c > a)
  (hs : s = (a + b + c) / 2) :
  a^2 + b^2 + c^2 ≥ √(s * (s - a) * (s - b) * (s - c)) * 4 * √3 := by
  -- Square the inequality
  suffices h : s * (s - a) * (s - b) * (s - c) * 48 ≤ (a^2 + b^2 + c^2)^2
  · calc
      _ = √(s * (s - a) * (s - b) * (s - c)) * (4 * √3) := by ring
      _ = √(s * (s - a) * (s - b) * (s - c)) * (√16 * √3) := by congr; rw [show (16 : ℝ) = 4^2 by norm_num, sqrt_sq]; linarith
      _ = √(s * (s - a) * (s - b) * (s - c) * 48) := by simp; left; rw [←sqrt_mul]; norm_num; linarith
      _ ≤ a^2 + b^2 + c^2 := sqrt_le_iff.mpr ⟨by positivity, h⟩
  rw [hs]
  -- Rearrange: we get a sum of squared terms, which is positive
  suffices (a^2 - b^2)^2 + (b^2 - c^2)^2 + (c^2 - a^2)^2 ≥ 0 by linarith
  positivity