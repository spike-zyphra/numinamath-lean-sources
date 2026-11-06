import Mathlib

open Set Real

theorem algebra_190550 {a b : ℝ} (ha : 0 ≤ a) (hb : a ≤ b)
    (hA : ∀ x ∈ Icc a (a + 1981), x ∈ Icc 0 2012)
    (hB : ∀ x ∈ Icc (b - 1014) b, x ∈ Icc 0 2012) :
    (a + 1981 - (b - 1014)) ≥ 983 := by
  have h1 : a + 1981 ≤ 2012 := by
    have hA' := hA (a + 1981) (by
      simp [mem_Icc]
      all_goals linarith
    )
    simp [mem_Icc] at hA'
    all_goals linarith
  have h2 : b - 1014 ≥ 0 := by
    have hB' := hB (b - 1014) (by
      simp [mem_Icc]
      all_goals linarith
    )
    simp [mem_Icc] at hB'
    all_goals linarith
  have hb1 : b ≤ 2012 := by
    have hB' := hB b (by
      simp [mem_Icc]
      all_goals linarith
    )
    simp [mem_Icc] at hB'
    all_goals linarith
  -- As $a + 1981 \leq 2012$ implies $a \leq 31$, and $b \geq 1014$ from $b - 1014 \geq 0$.
  -- The goal $a + 1981 - (b - 1014) \geq 983$ implies $a + 1981 + 1014 - b \geq 983$.
  -- So $a - b + 2995 \geq 983$ which reduces to $a \geq b - 2012$.
  -- Since $a \geq 0$ and $b \leq 2012$, this is precisely the required bound.
  -- Since Lean's linarith will be given all the constraints (0 ≤ a, a ≤ 31, 0 ≤ b ≤ 2012, b ≥ 1014) automatically to derive the required inequality.
  linarith
  all_goals linarith