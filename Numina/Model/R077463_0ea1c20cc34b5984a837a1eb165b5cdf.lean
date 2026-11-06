import Mathlib

/- Given vectors $\overrightarrow{a}$, $\overrightarrow{b}$ satisfy $\left| \overrightarrow{a}-\overrightarrow{b} \right|=3$, $\left| \overrightarrow{a}+2\overrightarrow{b} \right|=6$, ${{\overrightarrow{a}}^{2}}+\overrightarrow{a}\cdot \overrightarrow{b}-2{{\overrightarrow{b}}^{2}}=-9$, then $\left| \overrightarrow{b} \right|=$ ___        ___. -/
theorem algebra_11971 (a b : ℝ × ℝ) (h₀ : Real.sqrt ((a.1 - b.1)^2 + (a.2 - b.2)^2) = 3)
    (h₁ : Real.sqrt ((a.1 + 2 * b.1)^2 + (a.2 + 2 * b.2)^2) = 6) (h₂ : (a.1^2 + a.2^2) +
    (a.1 * b.1 + a.2 * b.2) - 2 * (b.1^2 + b.2^2) = -9) :
    Real.sqrt (b.1^2 + b.2^2) = Real.sqrt 7 := by

  have h₀' : (a.1 - b.1)^2 + (a.2 - b.2)^2 = 9 := by
    calc
      (a.1 - b.1)^2 + (a.2 - b.2)^2 = (Real.sqrt ((a.1 - b.1)^2 + (a.2 - b.2)^2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
      _ = 3 ^ 2 := by rw [h₀]
      _ = 9 := by norm_num

  have h₁' : (a.1 + 2 * b.1)^2 + (a.2 + 2 * b.2)^2 = 36 := by
    calc
      (a.1 + 2 * b.1)^2 + (a.2 + 2 * b.2)^2 = (Real.sqrt ((a.1 + 2 * b.1)^2 + (a.2 + 2 * b.2)^2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
      _ = 6 ^ 2 := by rw [h₁]
      _ = 36 := by norm_num

  have heq1 : (a.1^2 + a.2^2) + (b.1^2 + b.2^2) - 2 * (a.1 * b.1 + a.2 * b.2) = 9 := by
    nlinarith

  have heq2 : (a.1^2 + a.2^2) + 4 * (b.1^2 + b.2^2) + 4 * (a.1 * b.1 + a.2 * b.2) = 36 := by
    nlinarith

  have h3 : b.1^2 + b.2^2 = 7 := by
    nlinarith [h₂, heq1, heq2]

  rw [h3]
  all_goals 
    norm_num
    <;> try tauto