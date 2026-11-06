import Mathlib

theorem algebra_322437 {n : ℤ} (hn : n > 0) (A : ℚ) (hA : A^2 = 1 + 1 / (n^2) + 1 / ((n + 1)^2)) :
    A = (n^2 + n + 1) / (n^2 + n) ∨ A = -(n^2 + n + 1) / (n^2 + n) := by
  have h1 : (n : ℚ) > 0 := by exact_mod_cast hn
  have eq1 : (1 : ℚ) + 1 / (n ^ 2 : ℚ) + 1 / ((n + 1) ^ 2 : ℚ) =
      ((n ^ 2 + n + 1) / (n ^ 2 + n) : ℚ) ^ 2 := by
    have hx2 : (n + 1 : ℚ) > 0 := by linarith
    field_simp [show (n : ℚ) ≠ 0 by linarith, show (n + 1 : ℚ) ≠ 0 by linarith]
    ring_nf
    <;> field_simp
    <;> ring
  rw [eq1] at hA
  have eq2 : (A - ( (n ^ 2 + n + 1) / (n ^ 2 + n) : ℚ ) ) * (A + ( (n ^ 2 + n + 1) / (n ^ 2 + n) : ℚ ) ) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp eq2) with h3 h4
  · -- case $A - \frac{n^2 + n + 1}{n^2 + n} = 0$
    left
    have hx4 : A = ( (n^2 + n + 1) / (n^2 + n) : ℚ ) := by
      have hx5 : A - ( (n^2 + n + 1) / (n^2 + n) : ℚ ) = 0 := by
        simpa using h3
      linarith
    exact hx4
  · -- case $A + \frac{n^2 + n + 1}{n^2 + n} = 0$
    right
    have hx5 : A = -(n^2 + n + 1) / (n^2 + n) := by
      have hx6 : A + ( (n^2 + n + 1) / (n^2 + n) : ℚ ) = 0 := by
        simpa using h4
      have hx7 : A = - ( (n^2 + n + 1) / (n^2 + n) : ℚ ) := by
        linarith
      rw [show -((n^2 + n + 1) / (n^2 + n) : ℚ) = -(n^2 + n + 1) / (n^2 + n) by ring] at hx7
      linarith
    exact_mod_cast hx5