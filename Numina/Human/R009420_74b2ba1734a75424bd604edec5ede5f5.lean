import Mathlib

/- Let $x$ and $y$ be positive real numbers, and $2x+6y-xy=0$. Find the minimum value of $x+y$. -/
theorem algebra_9375 : IsLeast {a : ℝ | ∃ x y : ℝ, 0 < x ∧ 0 < y ∧ 2 * x + 6 * y - x * y = 0 ∧ x + y = a} (8 + 4 * √3) := by
  -- Split the problem into two parts
  -- 1. Prove that 8 + 4 * √3 can be achieved
  -- 2. Prove that 8 + 4 * √3 is the minimum value
  constructor
  . -- Set x = 2 + 2 * √3, y = 6 + 2 * √3
    use (6 + 2 * √3), (2 + 2 * √3)
    refine ⟨?_, ?_, ?_, ?_⟩
    . positivity
    . positivity
    . ring_nf
      simp
      norm_num
    . linarith
  . intro a ⟨x, y, hx, hy, h, ha⟩
    subst ha
    -- Change the given equation to
    -- 6 / x + 2 / y = 1
    replace h : 6 / x + 2 / y = 1 := by
      field_simp
      linarith
    -- Prove the AM-GM inequality
    have AMGM {a b} (ha : 0 ≤ a) (hb : 0 ≤ b) : a + b ≥ 2 * √(a * b) := by
      have h : 0 ≤ (√a - √b) ^ 2 := sq_nonneg _
      simp [sub_sq, ha, hb] at h
      simp [Real.sqrt_mul ha]
      linarith
    -- x + y
    -- = (x + y) * (6 / x + 2 / y)
    -- = 8 + 2 * x / y + 6 * y / x
    -- ≥ 8 + 2 * √((2 * x / y) * (6 * y / x))
    -- = 8 + 2 * √(2^2*3)
    -- = 8 + 4 * √3
    calc x + y = (x + y) * (6 / x + 2 / y) := by rw [h]; ring
           _ = 8 + 2 * x / y + 6 * y / x := by field_simp; ring
           _ ≥ 8 + 2 * √((2 * x / y) * (6 * y / x)) := by linarith [AMGM (by positivity : 2 * x / y ≥ 0) (by positivity : 6 * y / x ≥ 0)]
           _ = 8 + 2 * √(2^2*3) := by rw [(by field_simp; ring : (2 * x / y) * (6 * y / x) = 2^2*3)]
           _ = 8 + 4 * √3 := by simp[Real.sqrt_mul]; ring
