import Mathlib

/- Vind alle viertallen $(a, b, c, d)$ van reële getallen waarvoor geldt

$$
\begin{aligned}
& a b+c+d=3, \\
& b c+d+a=5, \\
& c d+a+b=2, \\
& d a+b+c=6 .
\end{aligned}
$$ -/
theorem algebra_605055 :
  {(a, b, c, d) : ℝ × ℝ × ℝ × ℝ | a * b + c + d = 3 ∧ b * c + d + a = 5 ∧ c * d + a + b = 2 ∧ d * a + b + c = 6} =
    {(2, 0, 0, 3)} := by
  ext ⟨a, b, c, d⟩
  simp
  constructor
  -- First, we verify that (2, 0, 0, 3) is a solution.
  swap
  {
    rintro ⟨rfl, rfl, rfl, rfl⟩
    norm_num
  }
  -- Now, let a, b, c, d satisfy the system of equations.
  rintro ⟨h₁, h₂, h₃, h₄⟩
  -- Subtract the first equation from the second, and the third from the fourth.
  have h₅ : (b - 1) * (c - a) = 2 := by linear_combination h₂ - h₁
  have h₆ : (1 - d) * (c - a) = 4 := by linear_combination h₄ - h₃
  -- Because c - a ≠ 0, we get 1 - d = 2 * (b - 1), in other words, 2 * b + d = 3.
  have h₇ : 1 - d = 2 * (b - 1) := by
    have h₈ : c - a ≠ 0 := by
      intro h
      simp [h] at h₅
    replace h₅ : b - 1 = 2 / (c - a) := by
      field_simp [h₅, h₈]
    replace h₆ : 1 - d = 4 / (c - a) := by
      field_simp [h₆, h₈]
    linear_combination h₆ - 2 * h₅
  replace h₇ : 2 * b + d = 3 := by linear_combination -h₇
  -- Subtract the third equation from the second, and the first from the fourth.
  have h₈ : (c - 1) * (b - d) = 3 := by linear_combination h₂ - h₃
  have h₉ : (1 - a) * (b - d) = 3 := by linear_combination h₄ - h₁
  -- Because b - d ≠ 0, we get c - 1 = 1 - a, in other words, a + c = 2.
  have h₁₀ : c - 1 = 1 - a := by
    have h₁₁ : b - d ≠ 0 := by
      intro h
      simp [h] at h₈
    replace h₈ : c - 1 = 3 / (b - d) := by
      field_simp [h₈, h₁₁]
    replace h₉ : 1 - a = 3 / (b - d) := by
      field_simp [h₉, h₁₁]
    linear_combination h₈ - h₉
  replace h₁₀ : a + c = 2 := by linear_combination h₁₀
  -- Sum the first and the second equation, and simplify using the value of a + c.
  have h₁₁ : (a + c) * (b + 1) + 2 * d = 8 := by linear_combination h₁ + h₂
  rw [h₁₀] at h₁₁
  -- Now b and d are determined, the rest is easy.
  obtain rfl : b = 0 := by linear_combination h₇ - h₁₁ / 2
  obtain rfl : d = 3 := by linear_combination h₇
  obtain rfl : c = 0 := by linear_combination h₁
  obtain rfl : a = 2 := by linear_combination h₂
  simp
