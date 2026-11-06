import Mathlib

/- What is the value of $b+c$ if $x^2+bx+c>0$ only when $x\in (-\infty, -2)\cup(3,\infty)$? -/
theorem algebra_20958 {b c : ℝ} (h : ∀ x, x^2 + b * x + c > 0 ↔ x < -2 ∨ x > 3) :
b + c = -7 := by
  -- $0 < b ^ 2 / 4 - c$
  have discrimgt : 0 < b ^ 2 / 4 - c := by
    -- For otherwise assume $b ^ 2 / 4 - c \le 0$
    by_contra contra
    rw [not_lt] at contra
    -- either $0 ^ 2 + b * 0 + c > 0$ or $1 ^2 + b * 1 + c > 0$
    have gt : 0 ^ 2 + b * 0 + c > 0 ∨ 1 ^2 + b * 1 + c > 0 := by
      -- For otherwise assume both are not greater than $0$
      by_contra contra1
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero, zero_add, gt_iff_lt, one_pow, mul_one, not_or, not_lt] at contra1
      -- $b = 0$
      have beq0 : b = 0 := by
        -- $(0 + b / 2) ^ 2 + c - b ^ 2 / 4 = 0$, and $(0 + b / 2) ^ 2 = 0$
        have eq2 : (0 + b / 2) ^ 2 = 0 := by
          have ge : 0 ≤ (0 + b / 2) ^ 2 := by
            exact sq_nonneg (0 + b / 2)
          linarith
        -- $b = 0$
        simp only [zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, div_eq_zero_iff, or_false] at eq2
        rw [eq2]
      -- $1 + b / 2 = 0$
      have beq1 : 1 + b / 2 = 0 := by
        -- $(1 + b / 2) ^ 2 = 0$
        have eq2 : (1 + b / 2) ^ 2 = 0 := by
          have ge : 0 ≤ (1 + b / 2) ^ 2 := by
            exact sq_nonneg (1 + b / 2)
          linarith
        simp only [zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, div_eq_zero_iff, or_false] at eq2
        rw [eq2]
      -- So $1 + 0 / 2 = 0$, a contradiction
      rw [beq0] at beq1
      linarith
    rcases gt with gt | gt
    -- If $0 ^ 2 + b * 0 + c > 0$, then by our assumption $0 < -2 \or 0 > 3$
    have := (h 0).mp gt
    rcases this with this | this
    linarith
    linarith
    -- If $1 ^ 2 + b * 1 + c > 0$, then by our assumption $1 < -2 \or 1 > 3$
    have := (h 1).mp gt
    rcases this with this | this
    linarith
    linarith
  -- $x ^ 2 + b * x + c > 0 = (x - (-b / 2 - \sqrt{b ^ 2 / 4 - c})) * (x - (-b / 2 + \sqrt{b ^ 2 / 4 - c}))$
  have eq : ∀ (x : ℝ), x ^ 2 + b * x + c = (x - (-b / 2 - Real.sqrt (b ^2 / 4 - c))) * (x - (-b / 2 + Real.sqrt (b ^2 / 4 - c))) := by
    intro x
    ring_nf
    rw [Real.sq_sqrt]
    ring_nf
    linarith
  -- $-b / 2 - \sqrt{b ^ 2 / 4 - c} = -2$
  have eq1 : -b / 2 - Real.sqrt (b ^ 2 / 4 - c) = -2 := by
    by_contra contra
    rcases lt_or_gt_of_ne contra with lt | lt
    -- $-b / 2 - \sqrt{b ^ 2 / 4 - c} < -2$ would leads to a contradiction
    have gt1 : (-b / 2 - Real.sqrt (b ^ 2 / 4 - c)) ^ 2 + b * (-b / 2 - Real.sqrt (b ^ 2 / 4 - c)) + c > 0 := by
      apply (h (-b / 2 - Real.sqrt (b ^ 2 / 4 - c))).mpr
      left
      linarith
    have eq1 : (-b / 2 - Real.sqrt (b ^ 2 / 4 - c)) ^ 2 + b * (-b / 2 - Real.sqrt (b ^ 2 / 4 - c)) + c = 0 := by
      rw [eq]
      ring
    linarith
    -- $-b / 2 - \sqrt{b ^ 2 / 4 - c} > -2$ would leads to a contradiction
    have gt2 : (-2) ^ 2 + b * (-2) + c > 0 := by
      rw [eq]
      have gt1 : -2 - (-b / 2 - √(b ^ 2 / 4 - c)) < 0 := by
        linarith
      have gt2 : -2 - (-b / 2 + √(b ^ 2 / 4 - c)) < 0 := by
        have gt3 : (-b / 2 - √(b ^ 2 / 4 - c)) < (-b / 2 + √(b ^ 2 / 4 - c)) := by
          apply add_lt_add_of_le_of_lt
          exact Preorder.le_refl (-b / 2)
          apply neg_lt_self
          exact Real.sqrt_pos_of_pos discrimgt
        linarith
      exact mul_pos_of_neg_of_neg gt1 gt2
    have := (h (-2)).mp gt2
    simp only [lt_self_iff_false, gt_iff_lt, false_or] at this
    linarith
  -- $-b / 2 + \sqrt{b ^ 2 / 4 - c} = 3$
  have eq2 : -b / 2 + Real.sqrt (b ^ 2 / 4 - c) = 3 := by
    by_contra contra
    rcases lt_or_gt_of_ne contra with lt | lt
    -- $-b / 2 + \sqrt{b ^ 2 / 4 - c} < 3$ would leads to a contradiction
    have gt1 : 3 ^ 2 + b * 3 + c > 0 := by
      rw [eq]
      have gt1 : 3 - (-b / 2 + √(b ^ 2 / 4 - c)) > 0 := by
        linarith
      have gt2 : 3 - (-b / 2 - √(b ^ 2 / 4 - c)) > 0 := by
        linarith
      exact (mul_pos_iff_of_pos_left gt2).mpr gt1
    have := (h 3).mp gt1
    simp only [gt_iff_lt, lt_self_iff_false, or_false] at this
    linarith
    -- $-b / 2 - \sqrt{b ^ 2 / 4 - c} > -2$ would leads to a contradiction
    have gt2 : (-b / 2 + Real.sqrt (b ^ 2 / 4 - c)) ^ 2 + b * (-b / 2 + Real.sqrt (b ^ 2 / 4 - c)) + c > 0 := by
      apply (h (-b / 2 + Real.sqrt (b ^ 2 / 4 - c))).mpr
      right
      linarith
    have eq2 : (-b / 2 + Real.sqrt (b ^ 2 / 4 - c)) ^ 2 + b * (-b / 2 + Real.sqrt (b ^ 2 / 4 - c)) + c = 0 := by
      rw [eq]
      ring
    linarith
  -- So $b = -1$
  have beq : b = -1 := by
    have mid : b = -(-b / 2 + -b / 2) := by
      ring
    apply eq_add_of_sub_eq at eq1
    apply eq_sub_of_add_eq at eq2
    nth_rw 1 [eq1, eq2] at mid
    rw [mid]
    ring
  -- $c = -6$, and so $b + c = -7$
  rw [add_comm] at eq2
  apply eq_sub_of_add_eq at eq2
  apply congrArg (fun x ↦ x ^2) at eq2
  rw [Real.sq_sqrt, beq] at eq2
  linarith
  exact le_of_lt discrimgt