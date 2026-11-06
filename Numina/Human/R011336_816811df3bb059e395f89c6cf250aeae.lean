import Mathlib

open Real

/- Let $a, b, c, d, e, f$ be non-negative real numbers satisfying $a+b+c+d+e+f=6$. Find the maximal possible value of


$$

a b c+b c d+c d e+d e f+e f a+f a b

$$


and determine all 6-tuples $(a, b, c, d, e, f)$ for which this maximal value is achieved.

Answer: 8 . -/
theorem inequalities_241709 :
    IsGreatest {x | ∃ a b c d e f : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ d ≥ 0 ∧ e ≥ 0 ∧ f ≥ 0 ∧ a + b + c + d + e + f = 6 ∧ x = a * b * c + b * c * d + c * d * e + d * e * f + e * f * a + f * a * b} 8 := by
    constructor
    -- let's show that 8 is obtainable
    · simp
      use 2;
      constructor; norm_num
      use 2;
      constructor; norm_num
      use 2;
      constructor; norm_num
      use 0;
      constructor; norm_num
      use 0;
      constructor; norm_num
      use 0;
      constructor; norm_num
      norm_num

    -- let's show that 8 is the maximum
    unfold upperBounds
    simp only [ge_iff_le, exists_and_left, Set.mem_setOf_eq, forall_exists_index, and_imp]
    intro sum a ha b hb c hc d hd e he f hf abcdef sumDef
    rw [sumDef]; clear sumDef
    -- use AM-GM
    calc a * b * c + b * c * d + c * d * e + d * e * f + e * f * a + f * a * b
    _ ≤ a * b * c + b * c * d + c * d * e + d * e * f + e * f * a + f * a * b + (a*c*e+b*d*f) := by simp; apply add_nonneg; apply mul_nonneg; apply mul_nonneg; assumption; assumption; assumption; apply mul_nonneg; apply mul_nonneg; assumption; assumption; assumption
    _ = (a+d)*(b+e)*(c+f) := by ring_nf
    _ ≤ (((a+d) + (b+e) + (c+f))/3)^3 := by
      have q:= Real.geom_mean_le_arith_mean3_weighted (w₁:=1/3) (w₂:=1/3) (w₃:=1/3) (p₁:=a+d) (p₂:=b+e) (p₃:=c+f) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith) (by norm_num)
      have q:= Real.rpow_le_rpow (z:=3) (by apply mul_nonneg; apply mul_nonneg; apply rpow_nonneg; linarith; apply rpow_nonneg; linarith; apply rpow_nonneg; linarith) q (by norm_num)
      conv_lhs at q =>
        calc _
        _ = ((a + d) ^ (1 / 3:ℝ)) ^ (3:ℝ) * ((b + e) ^ (1 / 3:ℝ)) ^ (3:ℝ) * ((c + f) ^ (1 / 3:ℝ)) ^ (3:ℝ) := by rw [Real.mul_rpow (by apply mul_nonneg; apply rpow_nonneg; linarith; apply rpow_nonneg; linarith) (by apply rpow_nonneg; linarith), Real.mul_rpow (by apply rpow_nonneg; linarith) (by apply rpow_nonneg; linarith)];
        _ = (a + d) * (b + e) * (c + f) := by rw [← Real.rpow_mul (by linarith), ← Real.rpow_mul (by linarith), ← Real.rpow_mul (by linarith)]; norm_num
      conv_rhs at q =>
        calc _
        _ = (((a + d) + (b + e) + (c + f))/3) ^ (3:ℝ) := by apply congr_arg (fun x => x^(3:ℝ)); ring_nf
        _ = (((a + d) + (b + e) + (c + f))/3) ^ 3 := by norm_cast
      exact q
    _ = ((a+b+c+d+e+f)/3)^3 := by ring_nf
    _ = 8 := by rw [abcdef]; norm_num;