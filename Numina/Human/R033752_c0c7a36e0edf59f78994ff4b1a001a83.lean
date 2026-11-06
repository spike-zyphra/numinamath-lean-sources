import Mathlib
open Real Set

/- Let $a>b>0$, then the minimum value of ${{a}^{2}}+\frac{1}{b(a-b)}$ is ( ).

A: $2$
B: $3$
C: $4$
D: $5$-/
theorem inequalities_623016 :
    IsLeast {x | ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a > b ∧ x = a ^ 2 + 1 / (b * (a - b))} 4 := by
  constructor
  · -- We need to show 4 belongs to the set.
    use Real.sqrt 2, Real.sqrt 2 / 2
    refine ⟨by positivity, by positivity, by norm_num, ?_⟩
    · ring_nf
      field_simp
      norm_num
  · -- Now we need to prove that 4 is the least element in the set.
    intro x hx
    rcases hx with ⟨a, b, ha, hb, hab, hx⟩
    apply sub_pos_of_lt at hab
    rw [hx]
    calc
      _ = (a ^ 2 * (b * (a - b)) + 1 - 4 * (b * (a - b))) / (b * (a - b)) + 4 := by
        -- First use field_simp to change the expression.
        field_simp
      _ ≥ 4 := by
        simp
        -- Show that a ^ 2 * (b * (a - b)) + 1 - 4 * (b * (a - b))) / (b * (a - b) ≥ 0.
        apply div_nonneg
        . -- We are basically using AM-GM inequality to get 4b(a - b) ≤ a², which is equivalent to 4ab ≤ a² + 4b² or (a - 2b)² ≥ 0; and (a - 2 / a)² ≥ 0, which is equivalent to (a² - 2)² ≥ 0.
          nlinarith [sq_nonneg (a - 2 * b), sq_nonneg (a ^ 2 - 2), show b * (a - b) > 0 by positivity]
        . positivity