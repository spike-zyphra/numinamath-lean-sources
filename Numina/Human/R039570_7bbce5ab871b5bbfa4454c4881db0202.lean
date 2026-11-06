import Mathlib

/-Let $a$ be the smallest positive integer, $b$ be the largest negative integer,
$c$ be the rational number with the smallest absolute value, and $d$ be the rational number whose reciprocal is equal to itself.
Find the value of $a^{2}-b^{2}+2d-c$.-/
theorem algebra_9410 {a b : ℤ} {c d: ℚ} (ha : IsLeast {x : ℤ | x > 0 } a)
    (hb : IsGreatest {x : ℤ | x < 0 } b)
    (hc : IsLeast {x : ℚ | ∃ y : ℚ, x = abs y} c ) (hd : d ≠ 0 ∧ d = d⁻¹) :
    a^2 - b^2 + 2 * d - c = 2 ∨ a^2 - b^2 + 2 * d - c = -2 := by
  replace ha : a = 1 := by
    have : IsLeast {x : ℤ | x > 0 } 1 := by tauto
    exact IsLeast.unique ha this
    -- $a$ is the smallest positive integer, so $a=1$.
  replace hb : b = -1 := by
    have : IsGreatest {x : ℤ | x < 0 } (-1) := by
      constructor
      · show -1 < 0
        norm_num
      · refine mem_upperBounds.mpr ?right.a
        intro x hx
        simp only [Set.mem_setOf_eq] at hx
        exact Lean.Omega.Int.add_le_zero_iff_le_neg.mp hx
    exact IsGreatest.unique hb this
    -- $b$ is the largest negative integer, which means $b=-1$.
  replace hc : c = 0 := by
    have : IsLeast {x : ℚ | ∃ y, x = abs y} 0 := by
      constructor
      · use 0
        rfl
      · refine mem_lowerBounds.mpr ?left.a
        intro x ⟨y, hy⟩
        exact hy ▸ abs_nonneg y
    exact IsLeast.unique hc this
    -- $c$ is the rational number with the smallest absolute value, thus $c=0$.
  replace hd : d = 1 ∨ d = -1 := by
    obtain ⟨h1, h2⟩ := hd
    have : d ^ 2 = 1 := by
      nth_rw 1 [pow_two, h2]
      exact Rat.inv_mul_cancel d h1
    exact sq_eq_one_iff.mp this
  -- $d$ is the rational number whose reciprocal is equal to itself, implying $d=\pm 1$.
  obtain rfl | rfl := hd
  · left
    calc
    a ^ 2 - ↑b ^ 2 + 2 * 1 - c = 1 ^ 2 - (-1) ^ 2 + 2 * 1 - 0 := by simp [ha, hb, hc]
    _ = 1 - 1 + 2 - 0 := by norm_num
    _ = 2 := by norm_num
  -- 1. When $d=1$:
  -- \begin{align*}
  -- a^{2}-b^{2}+2d-c &= 1^{2}-(-1)^{2}+2\cdot 1-0 \\
  -- &= 1 - 1 + 2 - 0 \\
  -- &= 2
  -- \end{align*}
  · right
    calc
    a ^ 2 - ↑b ^ 2 + 2 * -1 - c = 1 ^ 2 - (-1) ^ 2 + 2 * (-1) - 0 := by simp [ha, hb, hc]
    _ = 1 - 1 - 2 - 0 := by norm_num
    _ = -2 := by norm_num
  -- 2. When $d=-1$:
  -- \begin{align*}
  -- a^{2}-b^{2}+2d-c &= 1^{2}-(-1)^{2}+2\cdot (-1)-0 \\
  -- &= 1 - 1 - 2 - 0 \\
  -- &= -2
  -- \end{align*}
