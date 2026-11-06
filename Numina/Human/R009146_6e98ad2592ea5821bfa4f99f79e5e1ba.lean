import Mathlib

/- Yao Ming is $7\text{ ft and }5\text{ in}$ tall. His basketball hoop is $10$ feet from the ground. Given that there are
$12$ inches in a foot, how many inches must Yao jump to touch the hoop with his head? -/
theorem algebra_29045 (yao_tall : ℝ) (yao_tall_in : ℝ) (hoop : ℝ)
    (h : yao_tall = 7 * 12 + 5) (h' : hoop = 10 * 12) :
    hoop - yao_tall = 31 := by
  rw [h, h']
  linarith