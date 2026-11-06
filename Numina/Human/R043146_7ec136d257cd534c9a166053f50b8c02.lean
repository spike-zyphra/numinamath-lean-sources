import Mathlib

open Real Set

/- 9.109. Find the domain of the function $f$, if

$f(x)=\sqrt[6]{4^{\frac{x+1}{x}}-17 \cdot 2^{\frac{1}{x}}+4}$ -/
theorem algebra_170338 {f : ℝ → ℝ}
    (hf : f = λ x => (4 ^ ((x + 1) / x) - 17 * 2 ^ (1 / x) + 4) ^ ((1 : ℝ) / 6)) (x : ℝ) : 0 ≤ (4: ℝ) ^ ((x + 1) / x) - 17 * 2 ^ (1 / x) + 4 ∧ x ≠ 0 ↔ x ∈ Ico (-1 / 2) 0 ∪ Ioc 0 (1 / 2)  := by
  -- domain means square root and divisions are defined as how we normally use it
  -- first prove that rhs implies x ≠ 0
  have (h: x ∈ Ico (-1/2) 0 ∪ Ioc 0 (1/2)) : x ≠ 0 := by
    simp at h
    obtain h | h := h <;> linarith
  -- so we can simplify and put x ≠ 0 as a hypothesis of the iff
  rw [iff_self_and.mpr this]
  simp
  rintro h
  -- rewrite the division and 4 power to be (2^(x⁻¹))^2
  rw [show (x + 1)/x = 1 + 1/x by field_simp, rpow_add (by norm_num)]
  have : (4:ℝ)^(1/x) = (2^(x⁻¹))^2 := by
    rw [← rpow_natCast, ← rpow_mul (by norm_num), mul_comm, rpow_mul (by norm_num)]
    norm_num
  rw [this]
  -- now we'll do a chain of iffs
  calc
    -- change the lhs to a bound on square of linear expression
     _ ↔ (15/8)^2 ≤ ((2:ℝ)^x⁻¹ - 17/8)^2 := by
      constructor <;> (rintro h; linarith)
    -- convert to absolute values as lean has iff theorems for that
    _ ↔ 15/8 ≤ |(2:ℝ)^x⁻¹ - 17/8| := by
      rw [sq_le_sq, abs_eq_self.mpr (show (0:ℝ) ≤ 15/8 by norm_num)]
    -- convert _ ≤ |_| to two inequalities
    _ ↔ 15/8 ≤ (2:ℝ)^x⁻¹ - 17/8 ∨ 15/8 ≤ -((2:ℝ)^x⁻¹ - 17/8) := by rw [le_abs]
    -- convert to inequality with just 2's powers
    _ = (2^(2:ℝ) ≤ (2:ℝ)^x⁻¹ ∨ (2:ℝ)^x⁻¹ ≤ 2^(-2:ℝ)) := by
      congr 1 <;> simp only [eq_iff_iff]
      all_goals (constructor <;> (rintro h; linarith))
    -- simplify the powers to just inequalities of x⁻¹
    _ = (2 ≤ x⁻¹ ∨ x⁻¹ ≤ -2) := by
      congr 1 <;> simp only [eq_iff_iff]
      . exact Real.rpow_le_rpow_left_iff (by norm_num)
      . exact Real.rpow_le_rpow_left_iff (by norm_num)
    -- now depending on x < 0 or x > 0 convert two inquality to the interval conditins
    _ = (0 < x ∧ x ≤ 1/2 ∨ -1/2 ≤ x ∧ x < 0) := by
      obtain h | h := lt_or_gt_of_ne h
      . have h₁ : x ≤ 1/2 := by linarith
        have h₂ : ¬ 0 < x := by linarith
        have h₃ : ¬ 2 ≤ x⁻¹ := by
          suffices x⁻¹ < 0 by linarith
          simpa
        simp [-one_div, h₁, h, h₂, h₃]
        rw [← inv_le_inv_of_neg (by norm_num) (by simpa)]
        simp
        ring_nf
      . have h₁ : -1/2 ≤ x := by linarith
        have h₂ : ¬ x < 0 := by linarith
        have h₃ : ¬ x⁻¹ ≤ -2 := by
          suffices 0 < x⁻¹ by linarith
          simpa
        simp [-one_div, h₁, h, h₂, h₃]
        rw [← inv_le_inv₀ (by simpa) (by norm_num)]
        simp
    -- finally use tauto to move around propositions and prove the inequality
    _ ↔ _ := by
      ring_nf
      tauto