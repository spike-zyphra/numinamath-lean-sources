import Mathlib

/- Soit $x, y, z$ trois nombres réels vérifiant $x+y+z=2$ et $x y+y z+z x=1$. Déterminer la valeur maximale que peut prendre $x-y$. -/
theorem algebra_607240 :
    IsGreatest {r | ∃ x: ℝ, ∃ y: ℝ, ∃ z: ℝ, x + y + z = 2 ∧ x * y + y * z + z * x = 1 ∧ r = x - y } (2 / Real.sqrt 3) := by
  unfold IsGreatest upperBounds
  simp
  constructor
  -- show that $x = 2/3 + 1/\sqrt{3}$, $y = 2/3 - 1/\sqrt{3}$, $z = 2/3$ is a solution
  . use (2 / 3 + 1 / Real.sqrt 3)
    use (2 / 3 - 1 / Real.sqrt 3)
    use (2 / 3)
    ring_nf
    simp
    ring_nf
  . intro r x y z h₀ h₁ hr
    rw [hr]
    -- calculate $x ^ 2 + y ^ 2 + z ^ 2$ by squaring $x + y + z = 2$
    have sq_sum : x ^ 2 + y ^ 2 + z ^ 2 = 2 := by
      have h := congr_arg (λ x ↦ x ^ 2) h₀
      simp at h
      linear_combination h - 2 * h₁
    -- calculate $(x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2$
    have sub_sq_sum : (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 = 2 := by linear_combination 2 * sq_sum - 2 * h₁
    -- using quadratic-arithmetic inequality
    -- we get $(x - y) ^ 2 ≤ 2 * ((x - z) ^ 2 + (z - y) ^ 2)$
    have : ((x - z) + (z - y)) ^ 2 ≤ 2 * ((x - z) ^ 2 + (z - y) ^ 2) := add_sq_le
    simp at this
    -- get the maximum value of $(x - y) ^ 2$
    replace : (x - y) ^ 2 ≤ 4 / 3 := by linear_combination (this + 2 * sub_sq_sum) / 3
    replace : (x - y) ^ 2 ≤ (2 / Real.sqrt 3) ^ 2 := by
      apply le_trans this
      apply le_of_eq
      rw [sq]
      symm
      calc 2 / √3 * (2 / √3) = 4 / (√3 * √3) := by ring_nf
      _ = 4 / 3 := by simp
    -- get the maximum value of $x - y$
    replace : x - y ≤ 2 / Real.sqrt 3 := by
      have := abs_le_of_sq_le_sq this (by apply div_nonneg; norm_num; exact Real.sqrt_nonneg _)
      exact (abs_le.1 this).2
    exact this
