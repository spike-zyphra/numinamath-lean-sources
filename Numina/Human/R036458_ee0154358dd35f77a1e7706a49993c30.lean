import Mathlib

namespace algebra_197683

lemma frac_linear_transform_sub  {a b c d : ℝ} 
    {x₁ x₃ y₁ y₃ : ℝ}
    (hx₁ : c * x₁ + d ≠ 0)
    (hx₃ : c * x₃ + d ≠ 0)
    (h₁ : y₁ = (a * x₁ + b) / (c * x₁ + d))
    (h₃ : y₃ = (a * x₃ + b) / (c * x₃ + d)) :
    y₃ - y₁ = (x₃ - x₁) * (a * d - b * c) / ((c * x₁ + d) * (c * x₃ + d)) := 
  calc
    _ = _ := by rw [h₁, h₃] 
    -- y_{3}-y_{1}=\frac{a x_{3}+b}{c x_{3}+d}-\frac{a x_{1}+b}{c x_{1}+d}
    _ = (c * a * x₁ * x₃ + b * c * x₁ + a * d * x₃ + b * d - a * c * x₁ * x₃ - b * c * x₃ - a * d * x₁ - b * d)/ ((c * x₁ + d) * (c * x₃ + d)) := by 
    -- =\frac{c a x_{1} x_{3}+b c x_{1}+a d x_{3}+b d-a c x_{3} x_{1}-b c x_{3}-a d x_{1}-b d}{\left(c x_{3}+d\right)\left(c x_{1}+d\right)}
      rw [div_sub_div] 
      · linear_combination
      · exact hx₃
      · exact hx₁ 
    _ = (- b * c * (x₃ - x₁) + a * d * (x₃ - x₁))/ ((c * x₁ + d) * (c * x₃ + d)) := by linear_combination 
    -- =\frac{-b c\left(x_{3}-x_{1}\right)+a d\left(x_{3}-x_{1}\right)}{\left(c x_{3}+d\right)\left(c x_{1}+d\right)}
    _ = _ := by linear_combination -- =\frac{\left(x_{3}-x_{1}\right)(a d-b c)}{\left(c x_{3}+d\right)\left(c x_{1}+d\right)}

end algebra_197683 

open algebra_197683

/- 13(1089). The function $y$ of $x$ is given by the formula $y=\frac{a x+b}{c x+d}$, 
where $a d-b c \neq 0$. 
Let the values of the argument 
$x_{1}, x_{2}, x_{3}$, and $x_{4}$ correspond to 
the function values $y_{1}, y_{2}, y_{3}$, and $y_{4}$. 
Prove that
$$
\frac{y_{3}-y_{1}}{y_{3}-y_{2}}: \frac{y_{4}-y_{1}}{y_{4}-y_{2}}
=\frac{x_{3}-x_{1}}{x_{3}-x_{2}}: \frac{x_{4}-x_{1}}{x_{4}-x_{2}}
$$ -/
theorem algebra_197683 {a b c d : ℝ} (ha : a * d - b * c ≠ 0)
    (x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : ℝ)
    (hx₁ : c * x₁ + d ≠ 0)
    (hx₂ : c * x₂ + d ≠ 0)
    (hx₃ : c * x₃ + d ≠ 0)
    (hx₄ : c * x₄ + d ≠ 0)
    (hx₃x₂ : x₃ - x₂ ≠ 0)
    (hx₄x₁ : x₄ - x₁ ≠ 0)
    (hx₄x₂ : x₄ - x₂ ≠ 0)
    (h₁ : y₁ = (a * x₁ + b) / (c * x₁ + d))
    (h₂ : y₂ = (a * x₂ + b) / (c * x₂ + d))
    (h₃ : y₃ = (a * x₃ + b) / (c * x₃ + d))
    (h₄ : y₄ = (a * x₄ + b) / (c * x₄ + d)) :
    ((y₃ - y₁) / (y₃ - y₂)) / ((y₄ - y₁) / (y₄ - y₂)) =
    ((x₃ - x₁) / (x₃ - x₂)) / ((x₄ - x₁) / (x₄ - x₂)) := by
  -- y_{3}-y_{1}=\frac{\left(x_{3}-x_{1}\right)(a d-b c)}{\left(c x_{3}+d\right)\left(c x_{1}+d\right)}
  have hy₃y₁' := frac_linear_transform_sub hx₁ hx₃ h₁ h₃ 
  -- y_{3}-y_{2}=\frac{\left(x_{3}-x_{2}\right)(a d-b c)}{\left(c x_{3}+d\right)\left(c x_{2}+d\right)}
  have hy₃y₂' := frac_linear_transform_sub hx₂ hx₃ h₂ h₃
  -- y_{4}-y_{1}=\frac{\left(x_{4}-x_{1}\right)(a d-b c)}{\left(c x_{4}+d\right)\left(c x_{1}+d\right)}
  have hy₄y₁' := frac_linear_transform_sub hx₁ hx₄ h₁ h₄
  -- y_{4}-y_{2}=\frac{\left(x_{4}-x_{2}\right)(a d-b c)}{\left(c x_{4}+d\right)\left(c x_{2}+d\right)}
  have hy₄y₂' := frac_linear_transform_sub hx₂ hx₄ h₂ h₄
  have h1 : (y₃ - y₁) / (y₃ - y₂) = ((x₃ - x₁) / (x₃ - x₂)) * (c * x₂ + d) / (c * x₁ + d) := by
    rw [hy₃y₁', hy₃y₂']
    field_simp 
    ring 
  have h2 : (y₄ - y₁) / (y₄ - y₂) = ((x₄ - x₁) / (x₄ - x₂)) * (c * x₂ + d) / (c * x₁ + d) := by
    rw [hy₄y₁', hy₄y₂']
    field_simp 
    ring
  -- Имеем:
  -- $$ \begin{aligned} & \frac{y_{3}-y_{1}}{y_{3}-y_{2}}: \frac{y_{4}-y_{1}}{y_{4}-y_{2}}= \end{aligned} $$
  -- $$ \begin{aligned} & =\frac{x_{1}-x_{1}}{x_{3}-x_{2}}: \frac{x_{4}-x_{1}}{x_{4}-x_{2}} \end{aligned} $$
  rw [h1, h2]
  field_simp 
  ring 
  