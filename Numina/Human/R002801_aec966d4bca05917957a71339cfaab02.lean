import Mathlib

/- 11.9. Given non-zero numbers $a, b, c$. Prove that the inequality


$$

\left|\frac{b}{a}-\frac{b}{c}\right|+\left|\frac{c}{a}-\frac{c}{b}\right|+|b c+1|>1

$$
 -/

-- lemma that if a, b, c are nonzero then among a*b, b*c, c*a, there must be positive values, if not we can multiply and that is a non positive square hence 0, impossible
lemma l_exists_pos_in_three_pairwise_muls_of_ne_zero (a b c : ℝ) (ha : a ≠ 0)
    (hb : b ≠ 0) (hc : c ≠ 0) :  a * b > 0 ∨ b * c > 0 ∨ a * c > 0 := by
  by_contra h
  push_neg at h
  obtain ⟨hab, hbc, hac⟩ := h
  have h_prod : (a * b) * (b * c) * (a * c) ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos ?_ hac
    apply mul_nonneg_of_nonpos_of_nonpos hab hbc
  replace h_prod : (a * b * c) ^ 2 ≤ 0 := by linear_combination h_prod
  have h_prod_zero : (a * b * c) ^ 2 = 0 := by linarith [sq_nonneg (a * b * c)]
  simp [ha,hb,hc] at h_prod_zero

theorem inequalities_115490 (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    |b / a - b / c| + |c / a - c / b| + |b * c + 1| > 1 := by
  -- define d and notice target beocmes following
  let d := 1 / a - 1 / b - 1 / c
  convert_to |b * d + 1| + |c * d + 1| + |b * c + 1| > 1
  . congr <;> (simp [d]; field_simp; ring)
  -- if d = 0 then 1 + 1 + |..| is already greater then 1
  by_cases hd : d = 0
  . rw [hd]
    simp
    linarith [abs_nonneg (b * c + 1)]
  -- otherwise generalize d to e and then wlog b * e > 0, otherwise by the lemma we can prove b * c > 0 or c * e > 0 and use the result
  . generalize d = e at hd
    clear d
    wlog h : b * e > 0 generalizing b c e
    . have := l_exists_pos_in_three_pairwise_muls_of_ne_zero b c e hb hc hd
      simp [h] at this
      obtain h' | h' := this
      . have := this b e hb hd c hc h'
        ring_nf at this ⊢
        assumption
      . have := this c b hc hb e hd h'
        ring_nf at this ⊢
        assumption
    -- 1 < b * e + 1 then inequality is easy by absolute value inequalities
    have h_ineq : 1 < b * e + 1 := by linarith
    linarith [le_abs_self (b * e + 1), abs_nonneg (c * e + 1), abs_nonneg (b * c + 1)]