import Mathlib

/- Find all real values of $r$ that satisfy $\frac1r > \frac1{r-1} + \frac1{r-4}.$ (Give your answer in interval notation.) -/
theorem algebra_21050 {r : ℝ} (hr : r ≠ 0 ∧ r ≠ 1 ∧ r ≠ 4) :
    1 / r > 1 / (r - 1) + 1 / (r - 4) ↔ r ∈ Set.Iio (-2) ∪ Set.Ioo 0 1 ∪ Set.Ioo 2 4 := by
  have rpos : r - 1 ≠ 0 := by
    exact sub_ne_zero_of_ne hr.2.1
  have rpos2 : r - 4 ≠ 0 := by
    exact sub_ne_zero_of_ne hr.2.2
  constructor
  · -- if the inequality holds, then $r \in (-\infty, -2) \cup (0, 1) \cup (2, 4)$ 
    intro rle
    -- $\[\frac{-(r-2)(r+2)}{r(r-1)(r-4)} > 0$
    apply sub_pos.mpr at rle
    rw [div_add_div _ _ rpos rpos2, div_sub_div _ _ hr.1 (by exact mul_ne_zero rpos rpos2)] at rle
    have eq : 1 * ((r - 1) * (r - 4)) - r * (1 * (r - 4) + (r - 1) * 1) = - (r - 2) * (r + 2) := by
      ring
    rw [eq] at rle
    have rne2 : r ≠ 2 := by
      by_contra contra
      rw [contra] at rle
      norm_num at rle
    have rneneg2 : r ≠ -2 := by
      by_contra contra
      rw [contra] at rle
      norm_num at rle
    simp only [div_eq_mul_inv, mul_inv, ← mul_assoc, neg_mul, Left.neg_pos_iff] at rle
    rcases lt_or_gt_of_ne hr.2.2 with rlt4 | rgt4
    -- when $r < 4$
    rcases lt_or_gt_of_ne rne2 with rlt2 | rgt2
    -- when $r < 2$
    rcases lt_or_gt_of_ne hr.2.1 with rlt1 | rgt1
    -- when $r < 1$
    rcases lt_or_gt_of_ne hr.1 with rlt0 | rgt0
    -- when $r < 0$
    rcases lt_or_gt_of_ne rneneg2 with rltneg2 | rgtneg2
    -- when $r < -2$
    left
    left
    exact rltneg2
    -- when $-2 < r < 0$
    have le1 : r - 2 < 0 := by
      linarith
    have le2 : r + 2 > 0 := by
      linarith
    have le3 : r⁻¹ < 0 := by
      exact inv_lt_zero.mpr rlt0
    have le4 : (r - 1)⁻¹ < 0 := by
      exact inv_lt_zero.mpr (by linarith)
    have le5 : (r - 4)⁻¹ < 0 := by
      exact inv_lt_zero.mpr (by linarith)
    have le6 : (r - 2) * (r + 2) < 0 := by
      exact mul_neg_of_neg_of_pos le1 le2
    have le7 : (r - 2) * (r + 2) * r⁻¹ > 0 := by
      exact mul_pos_of_neg_of_neg le6 le3
    have le8 : (r - 2) * (r + 2) * r⁻¹ * (r - 1)⁻¹ < 0 := by
      exact mul_neg_of_pos_of_neg le7 le4
    have le9 : (r - 2) * (r + 2) * r⁻¹ * (r - 1)⁻¹ * (r - 4)⁻¹ > 0 := by
      exact mul_pos_of_neg_of_neg le8 le5
    linarith
    -- when $0 < r < 1$
    left
    right
    exact ⟨rgt0, rlt1⟩
    -- when $1 < r < 2$
    have le1 : r - 2 < 0 := by
      linarith
    have le2 : r + 2 > 0 := by
      linarith
    have le3 : r⁻¹ > 0 := by
      exact inv_pos_of_pos (by linarith)
    have le4 : (r - 1)⁻¹ > 0 := by
      exact inv_pos_of_pos (by linarith)
    have le5 : (r - 4)⁻¹ < 0 := by
      exact inv_lt_zero.mpr (by linarith)
    have le6 : (r - 2) * (r + 2) < 0 := by
      exact mul_neg_of_neg_of_pos le1 le2
    have le7 : (r - 2) * (r + 2) * r⁻¹ < 0 := by
      exact mul_neg_of_neg_of_pos le6 le3
    have le8 : (r - 2) * (r + 2) * r⁻¹ * (r - 1)⁻¹ < 0 := by
      exact mul_neg_of_neg_of_pos le7 le4
    have le9 : (r - 2) * (r + 2) * r⁻¹ * (r - 1)⁻¹ * (r - 4)⁻¹ > 0 := by
      exact mul_pos_of_neg_of_neg le8 le5
    linarith
    -- when $2 < r < 4$
    right
    exact ⟨rgt2, rlt4⟩
    -- when $r > 4$
    have le1 : r - 2 > 0 := by
      linarith
    have le2 : r + 2 > 0 := by
      linarith
    have le3 : r⁻¹ > 0 := by
      exact inv_pos_of_pos (by linarith)
    have le4 : (r - 1)⁻¹ > 0 := by
      exact inv_pos_of_pos (by linarith)
    have le5 : (r - 4)⁻¹ > 0 := by
      exact inv_pos_of_pos (by linarith)
    have le6 : (r - 2) * (r + 2) > 0 := by
      exact mul_pos le1 le2
    have le7 : (r - 2) * (r + 2) * r⁻¹ > 0 := by
      exact mul_pos le6 le3
    have le8 : (r - 2) * (r + 2) * r⁻¹ * (r - 1)⁻¹ > 0 := by
      exact mul_pos le7 le4
    have le9 : (r - 2) * (r + 2) * r⁻¹ * (r - 1)⁻¹ * (r - 4)⁻¹ > 0 := by
      exact mul_pos le8 le5
    linarith
  · -- if $r \in (-\infty, -2) \cup (0, 1) \cup (2, 4)$, then the inequality holds
    intro rin
    apply sub_pos.mp
    rw [div_add_div _ _ rpos rpos2, div_sub_div _ _ hr.1 (by exact mul_ne_zero rpos rpos2)]
    have eq : 1 * ((r - 1) * (r - 4)) - r * (1 * (r - 4) + (r - 1) * 1) = - (r - 2) * (r + 2) := by
        ring
    rw [eq]
    simp only [div_eq_mul_inv, mul_inv, ← mul_assoc, neg_mul, Left.neg_pos_iff]
    rcases rin with rin | rin
    rcases rin with rin | rin
    · -- when $r < -2$
      rw [Set.mem_Iio] at rin
      have le1 : r - 2 < 0 := by
        linarith
      have le2 : r + 2 < 0 := by
        linarith
      have le3 : r⁻¹ < 0 := by
        exact inv_lt_zero.mpr (by linarith)
      have le4 : (r - 1)⁻¹ < 0 := by
        exact inv_lt_zero.mpr (by linarith)
      have le5 : (r - 4)⁻¹ < 0 := by
        exact inv_lt_zero.mpr (by linarith)
      have le6 : (r - 2) * (r + 2) > 0 := by
        exact mul_pos_of_neg_of_neg le1 le2
      have le7 : (r - 2) * (r + 2) * r⁻¹ < 0 := by
        exact mul_neg_of_pos_of_neg le6 le3
      have le8 : (r - 2) * (r + 2) * r⁻¹ * (r - 1)⁻¹ > 0 := by
        exact mul_pos_of_neg_of_neg le7 le4
      have le9 : (r - 2) * (r + 2) * r⁻¹ * (r - 1)⁻¹ * (r - 4)⁻¹ < 0 := by
        exact mul_neg_of_pos_of_neg le8 le5
      exact le9
    · -- when $0 < r < 1$
      rw [Set.mem_Ioo] at rin
      have le1 : r - 2 < 0 := by
        linarith
      have le2 : r + 2 > 0 := by
        linarith
      have le3 : r⁻¹ > 0 := by
        exact inv_pos_of_pos (by linarith)
      have le4 : (r - 1)⁻¹ < 0 := by
        exact inv_lt_zero.mpr (by linarith)
      have le5 : (r - 4)⁻¹ < 0 := by
        exact inv_lt_zero.mpr (by linarith)
      have le6 : (r - 2) * (r + 2) < 0 := by
        exact mul_neg_of_neg_of_pos le1 le2
      have le7 : (r - 2) * (r + 2) * r⁻¹ < 0 := by
        exact mul_neg_of_neg_of_pos le6 le3
      have le8 : (r - 2) * (r + 2) * r⁻¹ * (r - 1)⁻¹ > 0 := by
        exact mul_pos_of_neg_of_neg le7 le4
      have le9 : (r - 2) * (r + 2) * r⁻¹ * (r - 1)⁻¹ * (r - 4)⁻¹ < 0 := by
        exact mul_neg_of_pos_of_neg le8 le5
      exact le9
    · -- when $2 r < 4$
      rw [Set.mem_Ioo] at rin
      have le1 : r - 2 > 0 := by
        linarith
      have le2 : r + 2 > 0 := by
        linarith
      have le3 : r⁻¹ > 0 := by
        exact inv_pos_of_pos (by linarith)
      have le4 : (r - 1)⁻¹ > 0 := by
        exact inv_pos_of_pos (by linarith)
      have le5 : (r - 4)⁻¹ < 0 := by
        exact inv_lt_zero.mpr (by linarith)
      have le6 : (r - 2) * (r + 2) > 0 := by
        exact mul_pos le1 le2
      have le7 : (r - 2) * (r + 2) * r⁻¹ > 0 := by
        exact mul_pos le6 le3
      have le8 : (r - 2) * (r + 2) * r⁻¹ * (r - 1)⁻¹ > 0 := by
        exact mul_pos le7 le4
      have le9 : (r - 2) * (r + 2) * r⁻¹ * (r - 1)⁻¹ * (r - 4)⁻¹ < 0 := by
        exact mul_neg_of_pos_of_neg le8 le5
      exact le9