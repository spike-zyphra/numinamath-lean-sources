import Mathlib

/- Let $a$, $b$, $c$, $d$, and $e$ be positive integers with $a+b+c+d+e=2010$ and let $M$ be the largest of the sum $a+b$, $b+c$, $c+d$ and $d+e$. What is the smallest possible value of $M$? -/
theorem algebra_16178 : IsLeast {M | ∃ a b c d e : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧ a + b + c + d + e = 2010 ∧ Finset.max' {a + b, b + c, c + d, d + e} (Finset.insert_nonempty _ _) = M} 671 := by
  -- We prove two goals:
  -- 1. M = 671 can be achieved
  -- 2. M = 671 is the smallest possible value
  constructor
  . -- Set a = 669, b = 1, c = 670, d = 1, e = 669
    use 669, 1, 670, 1, 669
    -- Simplify the goal
    simp [Finset.max']
  . -- Prove that any M is at least 671
    rintro M ⟨a, b, c, d, e, ha, hb, hc, hd, he, h, rfl⟩
    let M := Finset.max' {a + b, b + c, c + d, d + e} (Finset.insert_nonempty _ _)
    -- a + b ≤ M, b + c ≤ M, c + d ≤ M, d + e ≤ M
    have h1 : a + b ≤ M := Finset.le_max' _ _ (by simp)
    have h2 : b + c ≤ M := Finset.le_max' _ _ (by simp)
    have h3 : c + d ≤ M := Finset.le_max' _ _ (by simp)
    have h4 : d + e ≤ M := Finset.le_max' _ _ (by simp)
    -- c < M because b + c ≤ M and b > 0
    have hc2 : c < M := by
      clear * - hb h2
      clear_value M
      omega
    -- Thus from h1, hc2, h4, we have a + b + c + d + e < 3 * M
    have H : a + b + c + d + e < 3 * M := by linarith only [h1, hc2, h4]
    -- And from h, we have a + b + c + d + e = 2010
    rw [h] at H
    -- Thus M ≥ 671
    clear * - H
    omega
