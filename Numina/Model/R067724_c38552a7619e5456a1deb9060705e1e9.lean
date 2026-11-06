import Mathlib

/- If the value of $\frac{\dfrac{1}{x-1}-\dfrac{x-1}{{{x}^{2}}+x+1}}{-\dfrac{9{{x}^{2}}}{{{x}^{3}}-1}}$ is $\frac{2}{3}$, then the value of $x$ is ___          ___. -/
theorem algebra_2595 {x : ℝ} (hx : x ≠ 1) (hx2 : x ≠ 0) (h : (1 / (x - 1) - (x - 1) / (x ^ 2 + x + 1)) / (-9 * x ^ 2 / (x ^ 3 - 1)) = 2 / 3) :
    x = -1 / 2 := by

  have h1 : x - 1 ≠ 0 := by
    intro h2
    apply hx
    linarith

  have h2 : x ^ 2 + x + 1 ≠ 0 := by 
    have : x ^ 2 + x + 1 > 0 := by
      nlinarith [sq_nonneg (x + 1/2), sq_nonneg (x ^ 2), sq_nonneg (x + 1/2)]
    nlinarith

  have h3 : x ^ 3 - 1 ≠ 0 := by 
    by_contra h4
    have : x ^ 3 = 1 := by linarith
    have h4' : x ^ 3 - 1 = (x - 1) * (x ^ 2 + x + 1) := by ring 
    rw [h4'] at h4
    cases' (mul_eq_zero.mp h4) with h5 h6
    · 
      have : x = 1 := by linarith
      contradiction
    · 
      have : x ^ 2 + x + 1 = 0 := by linarith
      contradiction
  
  have eq1 : (1 / (x - 1) - (x - 1) / (x ^ 2 + x + 1)) = (3 * x) / ((x - 1) * (x ^ 2 + x + 1)) := by 
    field_simp [h1, h2]
    ring
    <;> field_simp [h1, h2]
    <;> ring_nf at *
    <;> field_simp [h1, h2] at *
    all_goals nlinarith

  have eq2 : (1 / (x - 1) - (x - 1) / (x ^ 2 + x + 1)) / (-9 * x ^ 2 / (x ^ 3 - 1)) = (-1 / (3 * x)) := by 
    rw [eq1]
    have h4 : x ^ 3 - 1 = (x - 1) * (x ^ 2 + x + 1) := by ring 
    rw [h4]
    field_simp [h1, h2, h4, hx2]
    <;> ring_nf at *
    <;> field_simp [h1, h2, h4, hx2] at *
    <;> nlinarith

  rw [eq2] at h 
  field_simp [hx2] at h 
  <;> nlinarith
  all_goals nlinarith