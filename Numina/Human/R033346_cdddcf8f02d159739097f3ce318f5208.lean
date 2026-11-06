import Mathlib

/- $4. $\frac{1}{a}=\frac{a+b+c+d+m}{a}=1+\frac{b}{a}+\frac{c}{a}+\frac{d}{a}+\frac{m}{a}$

$$
\begin{aligned}
& \frac{1}{b}=\frac{a+b+c+d+m}{b}=\frac{a}{b}+1+\frac{c}{b}+\frac{d}{b}+\frac{m}{b} \\
& \frac{1}{c}=\frac{a+b+c+d+m}{c}=\frac{a}{c}+1+\frac{b}{c}+\frac{d}{c}+\frac{m}{c}
\end{aligned}
$$

$\frac{1}{d}=\frac{a+b+c+d+m}{d}=\frac{a}{d}+\frac{b}{d}+\frac{c}{d}+1+\frac{m}{d}$

$\frac{1}{m}=\frac{a+b+c+d+m}{m}=\frac{a}{m}+\frac{b}{m}+\frac{c}{m}+\frac{d}{m}+1$

$\frac{1}{a}+\frac{1}{b}+\frac{1}{c}+\frac{1}{d}+\frac{1}{m}=5+\left(\frac{b}{a}+\frac{a}{b}\right)+\left(\frac{c}{a}+\frac{a}{c}\right)+\cdots+\left(\frac{m}{d}+\frac{d}{m}\right) \geq 5+2 \cdot 10=25$.

$\left(10\right.$ brackets of the form $x+\frac{1}{x} \geq 2$ when $\left.x>0\right)$ -/
theorem Inequalities_102070 (a b c d m : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (hm : 0 < m) (h : a + b + c + d + m = 1):
    1 / a + 1 / b + 1 / c + 1 / d + 1 / m ≥ 25:= by 
  have eq1 : 1 / a = 1 + b / a + c / a + d / a + m / a := by
    conv => 
      lhs 
      rw [←h]
    field_simp
  have eq2 : 1 / b = a / b + 1 + c / b + d / b + m / b := by
    conv =>
      lhs
      rw [←h]
    field_simp
  have eq3 : 1 / c = a / c + b / c + 1 + d / c + m / c := by
    conv =>
      lhs
      rw [←h]
    field_simp
  have eq4 : 1 / d = a / d + b / d + c / d + 1 + m / d := by
    conv =>
      lhs
      rw [←h]
    field_simp
  have eq5 : 1 / m = a / m + b / m + c / m + d / m + 1 := by
    conv =>
      lhs
      rw [←h]
    field_simp
  rw [eq1, eq2 ,eq3, eq4, eq5]
  have neq1 : a ≠ 0 := by 
    linarith
  have neq2 : b ≠ 0 := by linarith
  have ineq_aux (x y : ℝ) (hx : x ≥ 0) (hy : y ≥ 0): 
    x + y  ≥ 2 * (x * y) ^ ((1:ℝ) / 2) := by
      have aux1 : x + y = |x + y| := by 
        unfold abs
        simp
        linarith
      have aux2 : 2 * (x * y) ^ ((1:ℝ) / 2) = |2 * (x * y) ^ ((1:ℝ) / 2)| := by 
        unfold abs
        simp
        positivity
      rw [aux1, aux2]
      refine sq_le_sq.mp ?_
      have aux3 : (2 * (x * y) ^ (1 / (2 : ℝ))) ^ 2 = 4 * x * y := by
        ring_nf
        congr
        have aux4 : ((x * y) ^ (1 / (2 : ℝ))) ^ (2 : ℕ)
          = ((x * y) ^ (1 / (2 : ℝ))) ^ (2 : ℝ) := by norm_cast
        rw [aux4, ←Real.rpow_mul (by positivity) (1 / (2 : ℝ)) 2 (x := x * y)]
        simp
      rw [aux3]
      nlinarith [sq_nonneg (x - y)]
  have ineq1 : b / a + a / b ≥ 2 := by
    obtain h' := ineq_aux (b / a) (a / b) (by positivity) (by positivity)
    simp at h'
    field_simp at h'
    field_simp
    exact h'
  have ineq2 : c / a + a / c ≥ 2 := by
    obtain h' := ineq_aux (c / a) (a / c) (by positivity) (by positivity)
    simp at h'
    field_simp at h'
    field_simp
    exact h'
  have ineq3 : d /a + a / d ≥ 2 := by
    obtain h' := ineq_aux (d / a) (a / d) (by positivity) (by positivity)
    simp at h'
    field_simp at h'
    field_simp
    exact h'
  have ineq4 : m /a + a / m ≥ 2 := by 
    obtain h' := ineq_aux (m / a) (a / m) (by positivity) (by positivity)
    simp at h'
    field_simp at h'
    field_simp
    exact h'
  have ineq5 : c / b + b / c ≥ 2 := by
    obtain h' := ineq_aux (c / b) (b / c) (by positivity) (by positivity)
    simp at h'
    field_simp at h'
    field_simp
    exact h'
  have ineq6 : d / b + b / d ≥ 2 := by
    obtain h' := ineq_aux (d / b) (b / d) (by positivity) (by positivity)
    simp at h'
    field_simp at h'
    field_simp
    exact h'
  have ineq7 : m / b + b / m ≥ 2 := by
    obtain h' := ineq_aux (m / b) (b / m) (by positivity) (by positivity)
    simp at h'
    field_simp at h'
    field_simp
    exact h'
  have ineq8 : d / c + c / d ≥ 2 := by
    obtain h' := ineq_aux (d / c) (c / d) (by positivity) (by positivity)
    simp at h'
    field_simp at h'
    field_simp
    exact h'
  have ineq9 : m / c + c / m ≥ 2 := by
    obtain h' := ineq_aux (m / c) (c / m) (by positivity) (by positivity)
    simp at h'
    field_simp at h'
    field_simp
    exact h'
  have ineq10 : m / d + d / m ≥ 2 := by
    obtain h' := ineq_aux (m / d) (d / m) (by positivity) (by positivity)
    simp at h'
    field_simp at h'
    field_simp
    exact h'
  nlinarith
  