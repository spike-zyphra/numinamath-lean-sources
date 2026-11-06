import Mathlib

/- 12. (POL 1) If $a$ and $b$ are arbitrary positive real numbers and $m$ an integer, prove that

$$

\left(1+\frac{a}{b}\right)^{m}+\left(1+\frac{b}{a}\right)^{m} \geq 2^{m+1}

$$
 -/
theorem inequalities_258555 (a b : ℝ) (m : ℤ) (ha : 0 < a) (hb : 0 < b) :
    (1 + a / b : ℝ) ^ m + (1 + b / a : ℝ) ^ m ≥ 2 ^ (m + 1) := by
  -- Rewrite the inequality as
  -- 2 ^ (m + 1) ≤ ((b + a) ^ m * a ^ m + (a + b) ^ m * b ^ m) / (b ^ m * a ^ m)
  field_simp
  -- Define w(0) = w(1) = 1 / 2.
  let w : Fin 2 → ℝ := fun _ => 1 / 2
  -- Define p(0) = a, p(1) = b.
  let p : Fin 2 → ℝ
  | 0 => a
  | 1 => b
  -- Multiply both sides of the inequality by (a + b)^(-m) / 2 > 0.
  apply le_of_mul_le_mul_left _ (show 0 < (a + b) ^ (-m) / 2 by positivity)
  calc
    -- We have (a + b)^(-m) / 2 * 2^(m + 1) = (1 / 2 * a + 1 / 2 * b)^(-m).
    (a + b)^(-m) / 2 * 2^(m + 1) = (1 / 2 * a + 1 / 2 * b)^(-m) := by
        field_simp
        rw [zpow_add₀ (by norm_num)]
        ring
    -- (1 / 2 * a + 1 / 2 * b)^(-m) = (∑ i, w i • p i)^(-m).
    _ = (∑ i, w i • p i)^(-m) := by simp [w, p]
    -- Apply Jensen's inequality to the convex function x^(-m) and obtain
    -- (∑ i, w i • p i)^(-m) ≤ ∑ i, w i • ((p i)^(-m)).
    _ ≤ ∑ i, w i • ((p i)^(-m)) := by
        apply (convexOn_zpow (𝕜 := ℝ) (-m)).map_sum_le
        · simp [w]
        · simp [w]
        · intro i
          fin_cases i <;> simp [p, ha, hb]
    -- ∑ i, w i • ((p i)^(-m)) = 1 / 2 * a^(-m) + 1 / 2 * b^(-m).
    _ = 1 / 2 * a^(-m) + 1 / 2 * b^(-m) := by simp [w, p]
    -- Obtain the final result with algebraic simplifications.
    _ = (a + b)^(-m) / 2 * (((b + a)^m * a^m + (a + b)^m * b^m) / (b^m * a^m)) := by
        field_simp
        rw [add_comm a]
        ring