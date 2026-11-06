import Mathlib

open Real Set
open scoped BigOperators

/-The solution set of the inequality $2^{x^{2}-x} < 4$ is \_\_\_\_\_\_.-/

theorem algebra_9180 (x : ℝ) : (2 ^ (x ^ 2 - x) : ℝ ) < 4 ↔ x > -1 ∧ x < 2 := by
--Given $2^{x^{2}-x} < 4$,
  have w1 : (2 ^ (x ^ 2 - x) : ℝ ) < 4 ↔ x ^ 2 - x < 2 := by
    have h : (1 : ℝ) < (2 : ℝ) := by norm_num
    constructor
    · rintro k
      have h1 : (2 ^ (x ^ 2 - x) : ℝ ) <(2 ^ (2 : ℝ) : ℝ) := by
      --First, notice that $4 = 2^{2}$. Therefore, we can rewrite the inequality as $2^{x^{2}-x} < 2^{2}$.
        norm_num
        exact k
      exact (Real.rpow_lt_rpow_left_iff h).mp h1
    · rintro k
      have h1 : (2 ^ (x ^ 2 - x) : ℝ ) <(2 ^ (2 : ℝ) : ℝ) := by
        apply (Real.rpow_lt_rpow_left_iff h).mpr k
      norm_num at h1
      exact h1
  --Since $y=2^{x}$ is an increasing function, we can infer that $2^{x^{2}-x} < 2^{2} \leftrightarrow x^{2}-x < 2$.
  have w2 : x ^ 2 - x < 2 ↔ x > -1 ∧ x < 2 := by
    constructor
    · rintro h
      have h1 : x ^ 2 - x - 2 < 0 := by simp[h]
      have h2 : x ^ 2 - x - 2 = (x + 1) * (x - 2) := by ring
      rw[h2] at h1
      apply mul_neg_iff.mp at h1
      by_contra t
      have h3 : 0 < x + 1 ↔ x > -1 := by
        exact Iff.symm neg_lt_iff_pos_add
      have h4 : x - 2 < 0 ↔ x < 2 := by
        exact sub_neg
      rw[h3,h4] at h1
      have h5 : x + 1 < 0 ∧ 0 < x - 2 := by
        apply Classical.or_iff_not_imp_left.mp h1 t
      linarith
    · rintro h
      rcases h with ⟨ha,hb⟩
      have h1 : x + 1 > 0 := by
        exact neg_lt_iff_pos_add.mp ha
      have h2 : x - 2 < 0 := by
        exact sub_neg.mpr hb
      have h3 : (x + 1) * (x - 2) < 0 := by
        exact mul_neg_of_pos_of_neg h1 h2
      have h4 : x ^ 2 - x - 2 = (x + 1) * (x - 2) := by ring
      rw[← h4] at h3
      linarith
  --Solving the quadratic inequality $x^{2}-x < 2$, we find that $-1 < x < 2$.
  constructor
  · rintro h
    have h1 : x ^ 2 - x < 2 := by
      exact w1.mp h
    exact w2.mp h1
  · rintro h
    have h1 : x ^ 2 - x < 2 := by
      exact w2.mpr h
    exact w1.mpr h1
  --Therefore, the solution set is $(-1,2)$.
