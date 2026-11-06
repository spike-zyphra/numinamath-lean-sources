import Mathlib

/-Let $a,$ $b,$ and $c$ be positive real numbers such that $a^2 = bc$ and $a + b + c = abc.$  Find the smallest possible value of $a^2.$-/
theorem algebra_21393 : IsLeast {m | ∃a : ℝ, 0 < a ∧ ∃b : ℝ, 0 < b ∧∃c : ℝ, 0 < c ∧ a^2 = b * c ∧ a + b + c = a * b * c ∧ m = a ^ 2} 3 := by
  simp [IsLeast, lowerBounds]
  refine ⟨?_, ?_⟩
  -- show that 3 can be expressed
  . -- use that a = b = c = √3
    use √3
    simp
    use √3
    simp
    use √3
    simp
    ring
  -- show that 3 is the least
  . intro m a ha b hb c hc h2 hsum hm
    -- first prove the inequality of (a + b + c) ^ 3 ≥ 27 * a * b * c
    have am_gm : 27 * a * b * c ≤ (a + b + c) ^ 3:= by
      rw [<-sub_nonneg]
      -- show the result by equation (a + b + c) ^ 3 - 27abc = ∑_{cyc} 3a(b - c) ^ 2 + (a + b + c)(∑_{cyc} (a - b) ^ 2) / 2
      calc
        0 ≤ 3 * a * (b - c) ^ 2 + 3 * b * (c - a) ^ 2 + 3 * c * (a - b) ^ 2 + (a + b + c) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) * (1 /  2) := by positivity
        _ = (a + b + c) ^ 3 - 27 * a * b * c := by ring_nf
    -- substitute the expression of hsum
    rw [hsum] at am_gm
    -- show that a * b * c = a ^ 3
    have h3 : a * b * c = a ^ 3 := by
      rw [mul_assoc]
      rw [<-h2]
      ring_nf
    rw [mul_assoc, <-h2, h3] at am_gm
    ring_nf at am_gm
    -- show that a ^ 6 ≥ 27
    have ineq : a ^ 3 * 27 / a ^ 3 ≤ a ^ 9 / a ^ 3 := by
      apply div_le_div₀
      all_goals linarith
    field_simp at ineq
    rw [<-zpow_natCast_sub_natCast₀] at ineq
    norm_num at ineq
    norm_cast at ineq
    -- show that a ^ 6 = m ^ 3
    have eq : a ^ 6 = m ^ 3 := by rw [hm]; ring_nf
    rw [eq] at ineq
    replace ineq : 3 ^ 3 ≤ m ^ 3 := by linarith
    rw [pow_le_pow_iff_left₀] at ineq
    -- show that 3 ≤ m
    . exact ineq
    . norm_num
    . rw [hm]; nlinarith
    . norm_num
    . positivity
