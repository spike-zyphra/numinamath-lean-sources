import Mathlib

/- Wir betrachten alle positiven reellen Zahlen $a, b, c, d$, für die $(a+c)(b+d)=a c+b d$ gilt.
Bestimmen Sie den kleinsten Wert, den $S=\frac{a}{b}+\frac{b}{c}+\frac{c}{d}+\frac{d}{a}$ annehmen kann. -/
theorem algebra_605431 :
    IsLeast {x : ℝ | ∃ a b c d : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ (a + c) * (b + d) = a * c + b * d ∧ x = a / b + b / c + c / d + d / a} 8 := by
  -- Break the goal into two parts.
  simp [IsLeast, lowerBounds]
  refine ⟨?_, ?_⟩
  . -- Show that S = 8 works.
    -- Use (a, b, c, d) = (2 + √3, 1, 2 + √3, 1).
    iterate 2 use 2 + Real.sqrt 3, by positivity, 1, by norm_num
    field_simp
    ring_nf
    rw [Real.sq_sqrt (by norm_num)]
    ring_nf
    tauto
  . -- Show that S ≥ 8 always work.
    intro x a ha b hb c hc d hd h hx
    rw [hx]
    -- Prove the AM-GM inequality for two variables.
    have AM_GM₂ (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : x + y ≥ 2 * Real.sqrt (x * y) := by
      rw [ge_iff_le, <-sq_le_sq₀, mul_pow, Real.sq_sqrt]
      linarith only [sq_nonneg (x - y)]
      all_goals
        positivity
    rw [<-ge_iff_le]
    -- Apply AM-GM inequality for multiple times.
    calc
      a / b + b / c + c / d + d / a = (a / b + c / d) + (b / c + d / a) := by ac_rfl
      _ ≥ 2 * Real.sqrt (a / b * (c / d)) + 2 * Real.sqrt (b / c * (d / a)) := by
        -- Show that (a / b + c / d) + (b / c + d / a) ≥ 2√(a/b * (c/d)) + 2√(b/c * (d/a)) by applying AM-GM inequality.
        apply add_le_add
        all_goals
          apply AM_GM₂
          all_goals
            positivity
      _ = (2 * (a * c + b * d)) / Real.sqrt (a * b * c * d) := by
        -- Simplify the expression.
        field_simp
        rw [mul_assoc 2, mul_assoc 2]
        repeat rw [<-Real.sqrt_mul]
        rw [show (b * d * (c * a)) = a * b * c * d by ring, show a * c * (c * a) = (a * c) ^ 2 by ring, show b * d * (b * d) = (b * d) ^ 2 by ring]
        iterate 2 rw [Real.sqrt_sq]
        rw [<-mul_add]
        all_goals
          positivity
      _ = 2 * ((a + c) * (b + d) / Real.sqrt (a * b * c * d)) := by
        -- Use hypothesis (a + c)(b + d) = ac + bd.
        rw [h, mul_div_assoc]
      _ ≥ 2 * ((2 * Real.sqrt (a * c)) * (2 * Real.sqrt (b * d)) / Real.sqrt (a * b * c * d)) := by
        -- Apply AM-GM inequality again.
        rw [ge_iff_le, mul_le_mul_left (by norm_num), div_le_div_iff_of_pos_right (by positivity)]
        apply mul_le_mul
        . exact AM_GM₂ a c ha hc
        . exact AM_GM₂ b d hb hd
        all_goals
          positivity
      _ = 8 := by
        -- Simplify the expression.
        rw [mul_assoc, mul_comm (Real.sqrt (a * c)), mul_assoc, <-Real.sqrt_mul (by positivity), <-mul_assoc, <-mul_assoc, mul_div_assoc, show b * d * a * c = a * b * c * d by ring, div_self (by positivity)]
        norm_num

  