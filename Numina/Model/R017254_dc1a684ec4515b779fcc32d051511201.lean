import Mathlib

open Real
open scoped BigOperators

theorem inequalities_243848 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  |(a/b + b/c + c/a) - (a/c + c/b + b/a)| < 1 := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc
  -- Simplify expression to a single fraction
  have h2 : (a / b + b / c + c / a) - (a / c + c / b + b / a) =
      ((a - b) * (c - b) * (a - c)) / (a * b * c) := by
    field_simp [hb.ne.symm, ha.ne.symm, hc.ne.symm]
    ring_nf
    <;> field_simp [hb.ne.symm, ha.ne.symm, hc.ne.symm]
    <;> ring
  rw [h2]
  have h7 : |((a - b) * (c - b) * (a - c)) / (a * b * c)| < 1 := by
    have h8 : |((a - b) * (c - b) * (a - c)) / (a * b * c)| =
        |(a - b) * (c - b) * (a - c)| / |a * b * c| := by
      field_simp [abs_div]
      all_goals linarith [abs_nonneg ((a - b) * (c - b) * (a - c)), abs_nonneg (a * b * c)]
    rw [h8]
    have h9 : |(a - b) * (c - b) * (a - c)| =
        |a - b| * |c - b| * |a - c| := by
      simp [abs_mul]
      all_goals norm_num
      <;> ring
    have h10 : |a * b * c| = a * b * c := by
      have h11 : a * b * c > 0 := by positivity
      rw [abs_of_pos h11]
    rw [h9, h10]
    have h31 : |a - b| < c := by
      apply abs_sub_lt_iff.mpr
      constructor <;> linarith
    have h32 : |c - b| < a := by
      apply abs_sub_lt_iff.mpr
      constructor <;> linarith
    have h33 : |a - c| < b := by
      apply abs_sub_lt_iff.mpr
      constructor <;> linarith
    have h34 : |a - b| * |c - b| * |a - c| < a * b * c := by
      have h35 : |a - b| ≥ 0 := by apply abs_nonneg
      have h36 : |c - b| ≥ 0 := by apply abs_nonneg
      have h37 : |a - c| ≥ 0 := by apply abs_nonneg
      have h27 : 0 < a := ha
      have h28 : 0 < b := hb
      have h29 : 0 < c := hc
      -- Derive each inequality first
      have h38 : |a - b| * |c - b| < c * a := by
        nlinarith [abs_nonneg (a - b), abs_nonneg (c - b),
          sq_nonneg (a - b), sq_nonneg (c - b),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
      have h39 : |a - c| < b := by
        apply abs_sub_lt_iff.mpr
        constructor <;> linarith
      nlinarith [abs_nonneg (a - c), sq_nonneg (a - c),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    -- Apply div_lt_iff₀ to show the fraction is < 1 based on h34
    have h11 : |a - b| * |c - b| * |a - c| < a * b * c := h34
    have h12 : |a - b| * |c - b| * |a - c| / (a * b * c) < 1 := by
      apply (div_lt_iff₀ (by positivity)).mpr
      linarith
    linarith
  exact h7