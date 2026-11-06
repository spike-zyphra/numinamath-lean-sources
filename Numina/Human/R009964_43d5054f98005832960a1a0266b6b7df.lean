import Mathlib

open Real Set
open scoped BigOperators

/-Find the minimum value of
\[f(x) = x + \frac{x}{x^2 + 1} + \frac{x(x + 4)}{x^2 + 2} + \frac{2(x + 2)}{x(x^2 + 2)}\]for $x > 0.$-/
theorem algebra_11633 :
  IsLeast {x | ∃ y : ℝ, y > 0 ∧ x = y + y / (y ^ 2 + 1) + (y * (y + 4)) / (y ^ 2 + 2) +
    2 * (y + 2) / (y * (y ^ 2 + 2))} 5 := by
  simp [IsLeast, lowerBounds]
  -- first calculate the main equation to simplify the expression to am_gm form
  -- i.e simplify to (x(x^2+2)/(x^2+1)) + 4(x(x^2+2)/(x^2+1))⁻¹ + 1
  have eq₁(x : ℝ) (hx : 0 < x): x + x / (x ^ 2 + 1) + (x * (x + 4)) / (x ^ 2 + 2)  + 2 * (x + 2) / (x * (x ^ 2 + 2)) =
      x * (x ^ 2 + 2) / (x ^ 2 + 1) + 4 * ((x ^ 2 + 1) / (x * (x ^ 2 + 2))) + 1 := by
    calc x + x / (x ^ 2 + 1) + x * (x + 4) / (x ^ 2 + 2) + 2 * (x + 2) / (x * (x ^ 2 + 2)) =
      (x * (x ^ 2 + 1) + x) / (x ^ 2 + 1) + (x * (x + 4)) / (x ^ 2 + 2)  + 2 * (x + 2) / (x * (x ^ 2 + 2)) := by rw [add_div' x x (x ^ 2 + 1)]; positivity 
      _ = (x * (x ^ 2 + 1) + x) / (x ^ 2 + 1) + (x * (x * (x + 4)) / (x * (x ^ 2 + 2))  + 2 * (x + 2) / (x * (x ^ 2 + 2))) := by rw [mul_div_mul_left]; ring_nf; positivity
      _ = (x * (x ^ 2 + 1) + x) / (x ^ 2 + 1) + (x * (x * (x + 4)) + 2 * (x + 2)) / (x * (x ^ 2 + 2)) := by rw [<-add_div]
      _ = x * (x ^ 2 + 2) / (x ^ 2 + 1) + (4 * (x ^ 2 + 1) + x * (x ^ 2 + 2)) / (x * (x ^ 2 + 2)) := by ring_nf
      _ = x * (x ^ 2 + 2) / (x ^ 2 + 1) + 4 * (x ^ 2 + 1) / (x * (x ^ 2 + 2)) + (x * (x ^ 2 + 2)) / (x * (x ^ 2 + 2)) := by rw [add_div]; ring_nf
      _ = x * (x ^ 2 + 2) / (x ^ 2 + 1) + 4 * ((x ^ 2 + 1) / (x * (x ^ 2 + 2))) + 1 := by field_simp
  -- goal divides into two parts
  refine ⟨?_, ?_⟩
  pick_goal 2
  -- first prove the inequality
  . intro a x hx ha
    -- prove the AM-GM inequality
    have am_gm (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : √(4 * a * b) ≤ a + b := by
      rw [Real.sqrt_le_left];
      linarith only [show 0 ≤ (a - b) ^ 2 by positivity]
      positivity
    -- subsititute the (x(x^2+2)/(x^2+1)) and (x(x^2+2)/(x^2+1))⁻¹ to AM-GM inequality 
    have ineq₁ := am_gm (x * (x ^ 2 + 2) / (x ^ 2 + 1)) (4 * ((x ^ 2 + 1) / (x * (x ^ 2 + 2))))
    -- then we can calculate the inequality step by step
    have ha₁ : a - 1 ≥ 4 := by
      calc 
        a - 1= x * (x ^ 2 + 2) / (x ^ 2 + 1) + 4 * ((x ^ 2 + 1) / (x * (x ^ 2 + 2))) := by rw [ha, eq₁]; ring_nf; positivity
        _ ≥ √(4 * (x * (x ^ 2 + 2) / (x ^ 2 + 1)) * (4 * ((x ^ 2 + 1) / (x * (x ^ 2 + 2))))) := by apply ineq₁; repeat positivity
        _ = 4 := by field_simp; rw [show √4 = 2 by rw [<-@Real.sqrt_sq 2]; norm_num; positivity]; ring_nf
    linarith only [ha₁]
  -- then, prove the exsistence of being equal
  . -- show that there exsists a y > 0, y(y^2+2)/(y^2+1) = 2
    have intermediate : ∃ y : ℝ, 0 < y ∧ y * (y ^ 2 + 2) / (y ^ 2 + 1) = 2 := by
      set f : Polynomial ℝ := Polynomial.X ^ 3 - 2 * Polynomial.X ^ 2 + 2 * Polynomial.X - 2 with hf
      set g := fun x => f.eval x with hg
      -- show that polynomial is continuous
      have continuous₁ : Continuous g := by apply Polynomial.continuous
      -- then show the set form of intermediate value theorem
      have intermediate₁ : Set.Ioo (g 1) (g 2) ⊆ g ''Set.Ioo 1 2 := by
        apply intermediate_value_Ioo
        norm_num
        apply Continuous.continuousOn
        exact continuous₁
      -- calculate the g 1 and g 2 in the proposition
      nth_rewrite 1 2 [hg] at intermediate₁
      simp at intermediate₁
      rw [hf] at intermediate₁
      simp [Polynomial.eval_X] at intermediate₁
      norm_num at intermediate₁
      -- sepecially 0 ∈ g ((1, 2))
      rw [Set.subset_def] at intermediate₁
      have intermediate₀ : 0 ∈ g ''Set.Ioo 1 2 := by
        apply intermediate₁
        norm_num
      clear intermediate₁ continuous₁
      -- simplify 0 ∈ g((1, 2)) to ∃ 1 < y < 2, f y = 0
      simp at intermediate₀ 
      obtain ⟨y, hy, hy0⟩ := intermediate₀
      rw [hg] at hy0
      simp at hy0
      rw [hf] at hy0
      simp [Polynomial.eval_X] at hy0
      -- finally use y, so that ∃x, (x(x^2+2)/(x^2+1)) = 2
      use (y)
      refine ⟨?_, ?_⟩
      . linarith only [hy]
      . field_simp
        linarith only [hy0]
    -- substitute (y(y^2+2)/(y^2+1)) = 2 in the expression
    obtain ⟨y, hy, heq⟩ := intermediate
    use (y)
    refine ⟨?_, ?_⟩
    . exact hy
    . field_simp at heq
      rw [eq₁ y hy]
      rw [heq]
      field_simp
      ring_nf
  