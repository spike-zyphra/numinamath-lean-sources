import Mathlib

/- Let $x_1,x_2,y_1,y_2$ be real numbers satisfying the equations $x^2_1+5x^2_2=10$, $x_2y_1-x_1y_2=5$, and $x_1y_1+5x_2y_2=\sqrt{105}$. Find the value of $y_1^2+5y_2^2$ -/
theorem algebra_41370 (x1 x2 y1 y2 : ℝ)
    (h₀ : x1^2 + 5 * x2^2 = 10)
    (h₁ : x2 * y1 - x1 * y2 = 5)
    (h₂ : x1 * y1 + 5 * x2 * y2 = Real.sqrt 105) :
    y1^2 + 5 * y2^2 = 23 := by 
  have h₃ := congr_arg (fun x => x^2) h₁
  have h₄ := congr_arg (fun x => x^2) h₂
  ring_nf at h₃ h₄
  norm_num at h₃ h₄
  nlinarith [h₀, h₁, h₂, h₃, h₄]