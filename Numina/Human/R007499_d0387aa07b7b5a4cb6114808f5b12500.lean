import Mathlib

/- What is the value of $\frac{2013^3-2 \cdot 2013^2 \cdot 2014+3 \cdot 2013 \cdot 2014^2-2014^3+1}{2013 \cdot 2014}$? -/
theorem algebra_12285 : (2013^3 - 2 * 2013^2 * 2014 + 3 * 2013 * 2014^2 - 2014^3 + 1) / (2013 * 2014:ℝ) = 2013 := by
  -- let a = 2013, and therefore 2014=a+1.
  let a:= (2013:ℝ)
  have a_def: a = 2013 := rfl
  have h1: (2014:ℝ) = a+1 := by
    rw [a_def]; norm_num
  rw [← a_def, h1]
  -- separate the expression in two parts.
  let part1 := (3*a*(a+1)^2-2*a^2*(a+1))/(a*(a+1))
  have part1_def: part1 = (3*a*(a+1)^2-2*a^2*(a+1))/(a*(a+1)) := rfl
  let part2 := (a^3-(a+1)^3+1)/(a*(a+1))
  have part2_def: part2 = (a^3-(a+1)^3+1)/(a*(a+1)) := rfl
  have h2:  (a^3 - 2*a^2*(a+1) + 3*a*(a+1)^2 - (a+1)^3 + 1) / (a*(a+1)) =
    part1 + part2 := by
    have: (a^3 - 2*a^2*(a+1) + 3*a*(a+1)^2 - (a+1)^3 + 1) =
      (3*a*(a+1)^2-2*a^2*(a+1))+ (a^3-(a+1)^3+1) := by ring
    rw [this, part1_def, part2_def]; ring
  rw [h2]
  have nez: a*(a+1) ≠ 0 := by
    rw [a_def]; norm_num
  -- part1 simplifies to a+3
  have hp1: part1 = a+3 := by
    rw [part1_def]
    have ht1: 3*a*(a + 1)^2 - 2*a^2*(a + 1) = a*(a+1) * (3*(a+1)-2*a) := by ring
    have ht2: 3*(a+1)-2*a = a+3 := by ring
    rw [ht1,ht2]
    exact mul_div_cancel_left₀ (a + 3) nez
  -- for part2, we expand cube on the numerator. and it can simplifies to a.
  have hp2: part2 = -3 := by
    --expand cube on the numerator
    have ht1: a^3-(a+1)^3+1 = -3*(a*(a+1)) :=
    calc
      a^3-(a+1)^3+1 = a^3-(a^3+3*a^2+3*a+1)+1 := by ring
      _= a^3-a^3-3*a^2-3*a-1+1 := by ring
      _= -3*a^2-3*a := by ring
      _= -3*(a^2+a) := by ring
      _= -3*(a*(a+1)) := by ring
    rw [part2_def,ht1]
    exact mul_div_cancel_right₀ (-3) nez
  -- for part1=a+3 and part2=-3, substitute back.
  rw [hp1,hp2]
  -- the expression simplifies to a, or 2013. so the answer is 2013.
  simp