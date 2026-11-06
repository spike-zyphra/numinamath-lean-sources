import Mathlib

open Real

/- Let $a_{1}, a_{2}, \ldots, a_{n}$ be positive real numbers whose product is 1 . Show that the sum $\frac{a_{1}}{1+a_{1}}+\frac{a_{2}}{\left(1+a_{1}\right)\left(1+a_{2}\right)}+\frac{a_{3}}{\left(1+a_{1}\right)\left(1+a_{2}\right)\left(1+a_{3}\right)}+\cdots+\frac{a_{n}}{\left(1+a_{1}\right)\left(1+a_{2}\right) \cdots\left(1+a_{n}\right)}$ is greater than or equal to $\frac{2^{n}-1}{2^{n}}$. -/
theorem inequalities_605707 (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (h : ∏ i, a i = 1) :
    ∑ i, a i / (∏ j in Finset.univ.filter (· ≤ i), (1 + a j)) ≥ (2 ^ n - 1) / 2 ^ n := by
  -- Note for that every positive integer $m$,
  -- $$ \begin{aligned} \frac{a_{m}}{\left(1+a_{1}\right)\left(1+a_{2}\right) \cdots\left(1+a_{m}\right)} &
  -- =\frac{1+a_{m}}{\left(1+a_{1}\right)\left(1+a_{2}\right) \cdots\left(1+a_{m}\right)}-\frac{1}{\left(1+a_{1}\right)\left(1+a_{2}\right) \cdots\left(1+a_{m}\right)} \
  -- & =\frac{1}{\left(1+a_{1}\right) \cdots\left(1+a_{m-1}\right)}-\frac{1}{\left(1+a_{1}\right) \cdots\left(1+a_{m}\right)} . \end{aligned} $$
  have ham {m : Fin n} : a m / (∏ j in Finset.univ.filter (· ≤ m), (1 + a j)) =
      1 / (∏ j in Finset.univ.filter (fun j => j.val < m.val), (1 + a j)) - 1 / (∏ j in Finset.univ.filter (fun j => j.val < m.val + 1), (1 + a j)) := by
    rw [show a m = (1 + a m) - 1 by ring, sub_div]
    congr 1
    · have : Finset.univ.filter (· ≤ m) = Finset.univ.filter (fun j => j.val < m.val) ∪ {m} := by
        ext x
        simp
        exact le_iff_lt_or_eq
      rw [this, Finset.prod_union]
      · simp
        rw [div_mul_cancel_right₀]
        apply ne_of_gt
        apply add_pos (by simp)
        exact ha m
      · simp
    · congr
      ext x
      constructor <;> intro hx
      · exact Order.lt_add_one_iff.mpr hx
      · exact Fin.succ_le_succ_iff.mp hx
  -- Therefore, if we let $b_{j}=\left(1+a_{1}\right)\left(1+a_{2}\right) \cdots\left(1+a_{j}\right)$, with $b_{0}=0$, then by telescoping sums,
  let b (i : ℕ) := 1 / (∏ j in Finset.univ.filter (fun j => j.val < i), (1 + a j))
  have hb0 : b 0 = 1 := by simp [b]
  have ham' {m : Fin n} (_ : m ∈ Finset.univ) : a m / (∏ j in Finset.univ.filter (· ≤ m), (1 + a j)) = b m.val - b (m.val + 1) := by rw [ham]
  simp [ham']
  -- $$ \sum_{j=1}^{n} \frac{a_{j}}{\left(1+a_{1}\right) \cdots\left(1+a_{j}\right)}=\sum_{j=1}^{n}\left(\frac{1}{b_{j-1}}-\frac{1}{b_{j}}\right)=1-\frac{1}{b_{n}} $$
  have hneq : n = n - 1 + 1 := by rw [Nat.sub_add_cancel hn]
  rw [hneq]
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp [←sub_sub, ←hneq, hb0]
  simp only [sub_div, ne_eq, pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and, not_false_eq_true, div_self, one_div]
  apply sub_le_sub (by simp)
  simp [b]
  apply inv_le_inv₀ ?_ ?_|>.mpr
  -- Note that $b_{n}=\left(1+a_{1}\right)\left(1+a_{2}\right) \cdots\left(1+a_{n}\right)
  -- \geq\left(2 \sqrt{a_{1}}\right)\left(2 \sqrt{a_{2}}\right) \cdots\left(2 \sqrt{a_{n}}\right)=2^{n}$,
  -- with equality if and only if all $a_{i}$ 's equal to 1. Therefore,
  · have hamge {m : Fin n} : 1 + a m ≥ 2 * sqrt (a m) := by
      obtain h := geom_mean_le_arith_mean2_weighted (show 0 ≤ 1 / (2 : ℝ) by simp) (show 0 ≤ 1 / (2 : ℝ) by simp) (show 0 ≤ 1 by simp)
          (show 0 ≤ a m by apply le_of_lt; exact ha m) (by norm_num)
      rw [sqrt_eq_rpow]
      calc
        _ = 2 * (1 / 2 * 1 + 1 / 2 * a m) := by ring
        _ ≥ 2 * (1 ^ (1 / 2 : ℝ) * a m ^ (1 / 2 : ℝ)) := by rel [h]
        _ = _ := by simp
    trans ∏ j : Fin n, 2 * sqrt (a j)
    · simp [Finset.prod_mul_distrib, sqrt_eq_rpow]
      rw [Real.finset_prod_rpow _ _ (fun i _ => le_of_lt (ha i)), h]
      simp
    · apply Finset.prod_le_prod
      · simp
      · intro i _
        apply hamge
  · apply Finset.prod_pos
    intro i _
    apply add_pos (by simp) (ha i)
  · simp
