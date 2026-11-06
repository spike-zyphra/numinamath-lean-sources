import Mathlib
theorem algebra_604948 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 8) :
4 / 3 ≤ a ^ 2 / √((1 + a ^ 3) * (1 + b ^ 3)) + b ^ 2 / √((1 + b ^ 3) * (1 + c ^ 3)) +
c ^ 2 / √((1 + c ^ 3) * (1 + a ^ 3)):= by
  have h1 : ∀ x : ℝ, x > 0 → 1 / √(1 + x ^ 3) ≥ 2 / (2 + x ^ 2):= by
      intro x hx
      rw [show 1 / √(1 + x ^ 3) = |1 / √(1 + x ^ 3)| by exact Eq.symm (abs_of_nonneg (by positivity))]
      rw [show 2 / (2 + x ^ 2) = |2 / (2 + x ^ 2)| by exact Eq.symm (abs_of_nonneg (by positivity))]
      suffices (1 / √(1 + x ^ 3)) ^ 2 ≥ (2 / (2 + x ^ 2)) ^ 2 by exact sq_le_sq.mp this
      field_simp
      have g1 : (2 + x ^ 2) ^ 2 > 0:= by positivity
      norm_num
      field_simp
      suffices 4 ≤ (1 / (1 + x ^ 3)) * (2 + x ^ 2) ^ 2 by exact (div_le_iff₀ g1).mpr this
      have g2 : 1 + x ^ 3 > 0:= by positivity
      field_simp
      suffices 4 * (1 + x ^ 3) ≤ (2 + x ^ 2) ^ 2 by exact (le_div_iff₀ g2).mpr this
      suffices x ^ 2 * (x - 2) ^ 2 ≥ 0 by linarith
      positivity
  -- Apply the lemma to a, b, and c
  have h2:= h1 a ha
  have h3:= h1 b hb
  have h4:= h1 c hc
  clear h1
  -- Multiply inequalities pairwise
  have h5 : 1 / √(1 + a ^ 3) * (1 / √(1 + b ^ 3)) ≥ 2 / (2 + a ^ 2) * (2 / (2 + b ^ 2)):= by refine mul_le_mul h2 h3 (by positivity) (by positivity)
  have h6 : 1 / √(1 + b ^ 3) * (1 / √(1 + c ^ 3)) ≥ 2 / (2 + b ^ 2) * (2 / (2 + c ^ 2)):= by refine mul_le_mul h3 h4 (by positivity) (by positivity)
  have h7 : 1 / √(1 + c ^ 3) * (1 / √(1 + a ^ 3)) ≥ 2 / (2 + c ^ 2) * (2 / (2 + a ^ 2)):= by refine mul_le_mul h4 h2 (by positivity) (by positivity)
  clear h2 h3 h4
  -- Rewrite expressions to use the product form
  rw [show a ^ 2 / √((1 + a ^ 3) * (1 + b ^ 3)) = a ^ 2 * (1 / √(1 + a ^ 3) * (1 / √(1 + b ^ 3))) by field_simp]
  rw [show b ^ 2 / √((1 + b ^ 3) * (1 + c ^ 3)) = b ^ 2 * (1 / √(1 + b ^ 3) * (1 / √(1 + c ^ 3))) by field_simp]
  rw [show c ^ 2 / √((1 + c ^ 3) * (1 + a ^ 3)) = c ^ 2 * (1 / √(1 + c ^ 3) * (1 / √(1 + a ^ 3))) by field_simp]
  -- Prove positivity of squares
  have h2 : a ^ 2 > 0:= by positivity
  have h3 : b ^ 2 > 0:= by positivity
  have h4 : c ^ 2 > 0:= by positivity
  -- Apply multiplication to inequalities
  replace h5 : a ^ 2 * (1 / √(1 + a ^ 3) * (1 / √(1 + b ^ 3))) ≥ a ^ 2 * (2 / (2 + a ^ 2) * (2 / (2 + b ^ 2))):= by exact (mul_le_mul_iff_of_pos_left h2).mpr h5
  replace h6 : b ^ 2 * (1 / √(1 + b ^ 3) * (1 / √(1 + c ^ 3))) ≥ b ^ 2 * (2 / (2 + b ^ 2) * (2 / (2 + c ^ 2))):= by exact (mul_le_mul_iff_of_pos_left h3).mpr h6
  replace h7 : c ^ 2 * (1 / √(1 + c ^ 3) * (1 / √(1 + a ^ 3))) ≥ c ^ 2 * (2 / (2 + c ^ 2) * (2 / (2 + a ^ 2))):= by exact (mul_le_mul_iff_of_pos_left h4).mpr h7
  clear h2 h3 h4

  -- By transitivity, if we prove the lower bound for the right-hand side, we're done
  suffices a ^ 2 * (2 / (2 + a ^ 2) * (2 / (2 + b ^ 2))) + b ^ 2 * (2 / (2 + b ^ 2) * (2 / (2 + c ^ 2))) + c ^ 2 * (2 / (2 + c ^ 2) * (2 / (2 + a ^ 2))) ≥ 4 / 3 by linarith
  clear h5 h6 h7

  -- Simplify the expressions using field operations
  rw [show a ^ 2 * (2 / (2 + a ^ 2) * (2 / (2 + b ^ 2))) = 4 * a ^ 2 / ((2 + a ^ 2) * (2 + b ^ 2)) by field_simp ; linarith]
  rw [show b ^ 2 * (2 / (2 + b ^ 2) * (2 / (2 + c ^ 2))) = 4 * b ^ 2 / ((2 + b ^ 2) * (2 + c ^ 2)) by field_simp ; linarith]
  rw [show c ^ 2 * (2 / (2 + c ^ 2) * (2 / (2 + a ^ 2))) = 4 * c ^ 2 / ((2 + c ^ 2) * (2 + a ^ 2)) by field_simp ; linarith]

  -- Key transformation: Use c = 8/(ab) to rewrite the sum in a more manageable form
  rw [show 4 * a ^ 2 / ((2 + a ^ 2) * (2 + b ^ 2)) + 4 * b ^ 2 / ((2 + b ^ 2) * (2 + c ^ 2)) +
  4 * c ^ 2 / ((2 + c ^ 2) * (2 + a ^ 2)) = 4 * (a ^ 2 * (2 + c ^ 2) + b ^ 2 * (2 + a ^ 2) + c ^ 2 * (2 + b ^ 2)) / ((2 + a ^ 2) * (2 + b ^ 2) * (2 + c ^ 2)) by field_simp <;> ring]
  -- Assume equality holds and complete the proof
  have h2 : 2 + a ^ 2 > 0:= by positivity
  have h3 : 2 + b ^ 2 > 0:= by positivity
  have h4 : 2 + c ^ 2 > 0:= by positivity
  have h5 : (2 + a ^ 2) * (2 + b ^ 2) * (2 + c ^ 2) > 0:= by positivity
  suffices 4 * (a ^ 2 * (2 + c ^ 2) + b ^ 2 * (2 + a ^ 2) + c ^ 2 * (2 + b ^ 2)) ≥ (4 / 3) * ((2 + a ^ 2) * (2 + b ^ 2) * (2 + c ^ 2)) by exact (le_div_iff₀ h5).mpr this
  -- Final algebraic simplification leads to the desired result
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a * b - 4), sq_nonneg (b * c - 4), sq_nonneg (c * a - 4), sq_nonneg (a * b * c - 8), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]