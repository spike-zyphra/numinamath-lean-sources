import Mathlib

/-14. In the sequence $\left\{a_{n}\right\}$, $a_{7}=\frac{16}{3}$, and when $n \geqslant 2$, $a_{n}=\frac{3 a_{n-1}+4}{7-a_{n-1}}$.
(1) Does there exist a natural number $m$, such that when $n>m$, $a_{n} < 2$. If it exists, find the value of $m$; if not, explain the reason.
(2) When $n \geqslant 10$, prove that $\frac{a_{n-1}+a_{n+1}}{2}< a_{n}$.-/
theorem algebra_135834
    (a : ℕ → ℝ)
    (h7 : a 7 = 16 / 3)
    (han : ∀ n ≥ 2, a n = (3 * a (n - 1) + 4) / (7 - a (n - 1)))
    : (∃ m, ∀ n, m < n → a n < 2) ∧ ∀ n ≥ 10, (a (n - 1) + a (n + 1)) / 2 < a n := by

  -- 14. (1) 由 $a_{7}=\frac{16}{3}$, 及递推公式,可得 $a_{8}=12, a_{9}=-8$,
  have h_a_8 : a 8 = 12 := by
    rw [han]
    · simp [h7]
      norm_num
    · simp
  have h_a_9 : a 9 = -8 := by
    rw [han]
    · simp [h_a_8]
      norm_num
    · simp
  have h_a_10 : a 10 = -4 / 3 := by
    rw [han]
    · simp [h_a_9]
      norm_num
    · simp
  -- $$ a_{n-2}=\frac{3 a_{n-1}+4}{7-a_{n-1}}-2=\frac{3\left(a_{n-1}-2\right)}{7-a_{n-1}} \text {. } $$
  have h_lt_2_of_gt_8 {n : ℕ} (hn : n > 8) : a n < 2 := by
    induction n, hn using Nat.le_induction
    · rw [h_a_9]
      norm_num
    · rename_i n hn ih
      rw [han]
      · simp
        have : 7 - a n > 0 := by linarith only [ih]
        apply div_lt_iff₀ this |>.mpr
        apply sub_pos.mp
        apply lt_of_lt_of_eq (b := 5 * (2 - a n))
        · linarith only [ih]
        · ring
      · linarith only [hn]
  -- 所以若 $a_{n-1}2$. 综上所述,满足条件的 $m$ 存在,且 $m=8$.
  constructor
  · use 8
  · -- （2） $a_{10}=-\frac{4}{3}$, 易证当 $n \geqslant 10$ 时, $a_{n} \geqslant-\frac{4}{3}$.
    have h_a_n_gt_of_ge_10 {n : ℕ} (hn : n ≥ 10) : a n ≥ -4 / 3 := by
      induction n, hn using Nat.le_induction
      · rw [h_a_10]
      · rename_i n hn ih
        trans a n
        · rw [han]
          · apply sub_nonneg.mp
            have : 7 - a n > 0 := by
              simp
              trans 2
              · apply h_lt_2_of_gt_8
                linarith only [hn]
              · norm_num
            field_simp
            apply div_nonneg
            · ring_nf
              trans (2 - a n) ^ 2
              · positivity
              · apply le_of_eq
                ring
            · positivity
          · linarith only [hn]
        · exact ih
    -- $$ a_{n-1}+a_{n+1}-2 a_{n}=\left(\frac{7 a_{n}-4}{a_{n}+3}-a_{n}\right)+\left(\frac{3 a_{n}+4}{7-a_{n}}-a_{n}\right)=\frac{2\left(a_{n}-2\right)^{3}}{\left(7-a_{n}\right)\left(a_{n}+3\right)} \text {. } $$
    intro n hn
    have h₀ : a n + 3 > 0 := by linarith only [h_a_n_gt_of_ge_10 hn]
    have h₁ : a (n - 1) = (7 * a n - 4) / (a n + 3) := by
      field_simp
      suffices h : a n * (7 - a (n - 1)) = 3 * a (n - 1) + 4
      · symm
        apply sub_eq_zero.mp
        apply sub_eq_zero.mpr at h
        rw [←h]
        ring
      · rw [han, div_mul_cancel₀]
        · apply ne_of_gt
          simp
          trans 2
          · apply h_lt_2_of_gt_8
            apply Nat.lt_sub_of_add_lt
            simp
            exact hn
          · norm_num
        · linarith only [hn]
    have h₂ : a (n + 1) = (3 * a n + 4) / (7 - a n) := by rw [han]; simp; linarith only [hn]
    rw [h₁, h₂]
    have : 7 - a n > 0 := by
      simp
      trans 2
      · apply h_lt_2_of_gt_8
        linarith [hn]
      · norm_num
    apply sub_neg.mp
    apply lt_of_eq_of_lt (b := (a n - 2) ^ 3 / (7 - a n) / (a n + 3))
    · field_simp
      ring
    · -- 当 $n \geqslant 10$ 时, $a_{n}-20,7-a_{n}>0$, 所以 $\frac{a_{n-1}+a_{n+1}}{2}<a_{n}$.
      apply div_neg_of_neg_of_pos ?_ h₀
      apply div_neg_of_neg_of_pos ?_ this
      apply Odd.pow_neg_iff ?_ |>.mpr
      · simp
        apply h_lt_2_of_gt_8
        linarith only [hn]
      · exact Nat.odd_iff.mpr rfl
