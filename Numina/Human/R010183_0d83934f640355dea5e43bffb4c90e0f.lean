import Mathlib
open Mathlib
/-- Define a sequence recursively by $t_1 = 20$, $t_2 = 21$, and\[t_n = \frac{5t_{n-1}+1}{25t_{n-2}}\]for all $n \ge 3$. Then $t_{2020}$ can be expressed as $\frac{p}{q}$, where $p$ and $q$ are relatively prime positive integers. Find $p+q$. -/
theorem algebra_98335 {t : ℕ → ℚ}
(ht1 : t 1 = 20) (ht2 : t 2 = 21)
(h : ∀ n ≥ 3, t n = (5 * t (n - 1) + 1) / (25 * t (n - 2))) (p q : ℕ) (hp : p > 0) (hq : q > 0) (hr : p.Coprime q) (hf : t 2020 = p / q) : p + q = 626 := by
  -- https://artofproblemsolving.com/wiki/index.php/2020_AIME_II_Problems/Problem_6
  -- By substitution, we find $s_3 = \frac{53}{50}$, $s_4=\frac{103}{105\cdot50}$, $s_5=\frac{101}{105}$, $s_6=100$, and $s_7=105$.
  have ht3 := h 3 (by decide)
  simp only [ht1, ht2] at ht3; norm_num at ht3
  have ht4 := h 4 (by decide)
  simp only [ht1, ht2, ht3] at ht4; norm_num at ht4
  have ht5 := h 5 (by decide)
  simp only [ht1, ht2, ht3, ht4] at ht5; norm_num at ht5
  have ht6 := h 6 (by decide)
  simp only [ht1, ht2, ht3, ht4, ht5] at ht6; norm_num at ht6
  have ht7 := h 7 (by decide)
  simp only [ht1, ht2, ht3, ht4, ht5, ht6] at ht7; norm_num at ht7
  -- So $s_n$ has a period of $5$.
  have stairs (n : ℕ) : t (5 * (n + 1)) = t 5 ∧ t (5 * (n + 1) + 1) = t 6 ∧ t (5 * (n + 1) + 2) = t 7 := by
    induction n with
    | zero => norm_num
    | succ n IH =>
      obtain ⟨i1, i2, i3⟩ := IH
      simp only [h (5 * (n + 1 + 1)) (by omega)]
      ring_nf
      ring_nf at i1 i2 i3
      rw [(by omega : 10 + n * 5 - 1 = 9 + n * 5), (by omega : 10 + n * 5 - 2 = 8 + n * 5)]
      have tt := h (8 + n * 5) (by omega)
      have rr := h (9 + n * 5) (by omega)
      have rt := h (10 + n * 5) (by omega)
      have tr := h (11 + n * 5) (by omega)
      have xx := h (12 + n * 5) (by omega)
      ring_nf at tt rr rt tr
      simp only [(by omega : 8 + n * 5 - 1 = 7 + n * 5), (by omega : 8 + n * 5 - 2 = 6 + n * 5), (by omega : 9 + n * 5 - 1 = 8 + n * 5), (by omega : 9 + n * 5 - 2 = 7 + n * 5), (by omega : 10 + n * 5 - 1 = 9 + n * 5), (by omega : 10 + n * 5 - 2 = 8 + n * 5), (by omega : 11 + n * 5 - 1 = 10 + n * 5), (by omega : 11 + n * 5 - 2 = 9 + n * 5), (by omega : 12 + n * 5 - 1 = 11 + n * 5), (by omega : 12 + n * 5 - 2 = 10 + n * 5)] at tt rr rt tr
      simp only [tt] at rr
      simp only [tt, rr] at rt
      simp only [tt, rr, rt] at tr
      simp only [tt, rr, rt, tr] at xx
      simp only [tt, rr, tr, rt, xx, i1, i2, i3, ht4, ht5, ht6, ht7]
      norm_num
      rw [(by omega : 12 + n * 5 - 2 = 10 + n * 5)]
      simp only [tt, rr, tr, rt, xx, i1, i2, i3, ht4, ht5, ht6, ht7]
      norm_num
  -- Thus $s_{2020}=s_5=\frac{101}{105}$.
  have gat := (stairs 403).1
  rw [ht5] at gat
  norm_num at gat
  rw [hf] at gat
  obtain ⟨t1, t2⟩ := @Rat.div_int_inj p q 101 525 (by linarith) (by decide) (by simp only [Int.natAbs_ofNat]; exact hr) (by decide) (by simp only [Int.cast_natCast, Int.cast_ofNat]; exact gat)
  norm_cast at t1 t2
  subst p
  subst q
  -- $\frac{101}{105\cdot 5}\implies 101+525=\boxed{626}$.
  norm_num