import Mathlib
open Real

/- \section*{Aufgabe 2 - 171212}

Man ermittle alle reellen Lösungen $(x, y)$ des Gleichungssystems


$$

\begin{aligned}
2 \cdot \sqrt{x+y}+x+y & =8 \\
x^{3}+y^{3} & =40
\end{aligned}

$$


 -/
theorem algebra_197754 {x y : ℝ} (hpos : x + y ≥ 0) (h1 : 2 * √(x + y) + x + y = 8) (h2 : x ^ 3 + y ^ 3 = 40) :
  (x = 2 + √2 ∧ y = 2 - √2) ∨ (x = 2 - √2 ∧ y = 2 + √2) := by
  -- factor the first equation
  have h1 : (√(x + y) + 4) * (√(x + y) - 2) = 0 := by calc
    _ = 2 * √(x + y) + (√(x + y))^2 - 8 := by ring
    _ = 0 := by rw [sq_sqrt hpos, ←h1]; ring
  rcases mul_eq_zero.mp h1 with hxy | hxy
  -- we can't have √(x + y) + 4 = 0
  · absurd calc
      -4 = √(x + y) := by linarith [hxy]
      _ ≥ 0 := sqrt_nonneg _
    linarith
  have xy_val : (√(x + y))^2 = 4 := by nlinarith [hxy]
  rw [sq_sqrt hpos] at xy_val
  have y_val : y = 4 - x := by linarith [xy_val]
  rw [y_val] at h2
  -- factor the second equation
  have : (x - 2)^2 = (√2)^2 := by calc
    _ = (x^3 + (4 - x)^3 - 40) / 12 + 2 := by ring
    _ = (√2)^2 := by rw [h2]; nth_rewrite 1 [←sq_sqrt zero_le_two]; ring
  -- conclude
  rw [sq_eq_sq_iff_eq_or_eq_neg] at this
  rcases this with x_val | x_val
  · left; constructor <;> linarith
  · right; constructor <;> linarith