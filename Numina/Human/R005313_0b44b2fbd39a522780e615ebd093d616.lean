import Mathlib

/- Soit $x$ un réel strictement positif tel que $x^{5}-x^{3}+x \geq 3$. Prouver que $x^{6} \geq 5$. -/
theorem inequalities_607575 (x : ℝ) (hx : 0 < x) (h : x ^ 5 - x ^ 3 + x ≥ 3) : x ^ 6 ≥ 5 := by
  -- It suffices to prove that x ^ 6 + 1 ≥ 6.
  suffices x ^ 6 + 1 ≥ 6 by linarith
  calc
    -- x ^ 6 + 1 = (x ^ 2 + 1) * (x ^ 4 - x ^ 2 + 1)
    -- = (x + 1 / x) * (x ^ 5 - x ^ 3 + x)
    _ = (x + 1 / x) * (x ^ 5 - x ^ 3 + x) := by field_simp;ring
    _ ≥ 6 := by
      -- x + 1 / x ≥ 2 from AM-GM
      have h₁ : x + 1 / x ≥ 2 := by
        have k := two_mul_le_add_sq √x (1 / √x)
        simp [ne_of_gt hx, le_of_lt hx] at k ⊢
        exact k
      -- x ^ 5 - x ^ 3 + x ≥ 3 from the given inequality
      -- So (x + 1 / x) * (x ^ 5 - x ^ 3 + x) ≥ 6
      nlinarith only [h₁, h]
