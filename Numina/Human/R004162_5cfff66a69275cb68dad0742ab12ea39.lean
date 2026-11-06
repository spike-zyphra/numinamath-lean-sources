import Mathlib
open Finset

/- Let $a_{1}, a_{2}, \ldots, a_{n}$ be positive real numbers such that $\sum_{i=1}^{n} a_{i}^{3}=3$ and $\sum_{i=1}^{n} a_{i}^{5}=5$. Prove that $\sum_{i=1}^{n} a_{i}>\frac{3}{2}$. -/
theorem inequalities_240219 (n : ℕ) (hn : 0 < n) (a : ℕ → ℝ)
    (ha : ∀ i, 0 < a i) (h1 : ∑ i∈Icc 1 n, (a i)^3 = 3) (h2 : ∑ i∈Icc 1 n, (a i)^5 = 5) :
    ∑ i∈Icc 1 n, a i > 3 / 2 := by
    -- By Hölder's inequality, $$ \sum_{i=1}^{n} a^{3}=\sum_{i=1}^{n}\left(a_{i} \cdot a_{i}^{2}\right) \leqslant\left(\sum_{i=1}^{n} a_{i}^{5 / 3}\right)^{3 / 5} \cdot\left(\sum_{i=1}^{n}\left(a_{i}^{2}\right)^{5 / 2}\right)^{2 / 5} . $$
    have h1' : ∑ i∈Icc 1 n,(a i) ^ 3 = ∑ i∈Icc 1 n,(a i * (a i) ^ (2:ℝ)) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Real.rpow_two,pow_two,pow_three]
    have h2' : ∑ i∈Icc 1 n,(a i * (a i) ^ (2:ℝ)) ≤ (∑ i∈Icc 1 n,|a i|^(5/3:ℝ))^(1/(5/3:ℝ)) * (∑ i∈Icc 1 n,|(a i)^(2:ℝ)|^(5/2:ℝ))^(1/(5/2:ℝ)) := by
      apply Real.inner_le_Lp_mul_Lq
      refine (Real.isConjExponent_iff (5 / 3) (5 / 2)).mpr ?_
      norm_num
    -- We will show that $$ \sum_{i=1}^{n} a_{i}^{5 / 3} \leqslant\left(\sum_{i=1}^{n} a_{i}\right)^{5 / 3} $$
    have h3 : ∑ i ∈ Icc 1 n, |a i| ^ (5 / 3:ℝ) ≤ (∑ i ∈ Icc 1 n, |a i|) ^ (5 / 3:ℝ) := by
      -- Let $S=\sum_{i=1}^{n} a_{i}$, then (4) is equivalent to
      let S := ∑ i ∈ Icc 1 n, |a i|
      have hS : 0 < S := by
        simp [S]
        apply Finset.sum_pos
        intro i hi ;simp ;exact ne_of_gt (ha i) ;simp ;exact hn
      -- $$ \sum_{i=1}^{n}\left(\frac{a_{i}}{S}\right)^{5 / 3} \leqslant 1=\sum_{i=1}^{n} \frac{a_{i}}{S} $$
      -- which holds since $01$ yield $\left(\frac{a_{i}}{S}\right)^{5 / 3} \leqslant \frac{a_{i}}{S}$.
      have : ∑ i ∈ Icc 1 n, (|a i|/S) ^ (5 / 3:ℝ ) ≤ (∑ i ∈ Icc 1 n, |a i|/S) ^ (5 / 3:ℝ) := by
        have : (∑ i ∈ Icc 1 n, |a i|/S) ^ (5 / 3:ℝ) = ∑ i ∈ Icc 1 n, |a i|/S := by
          rw [← Finset.sum_div] ;simp [S] ;rw [div_self] ;simp
          have : 0 < ∑ i ∈ Icc 1 n, |a i| := by exact hS
          exact Ne.symm (ne_of_lt hS)
        rw [this]
        apply Finset.sum_le_sum
        intro i hi
        have : 0 ≤ (|a i| / S) ∧ (|a i| / S) ≤ 1 := by
          constructor
          · refine div_nonneg (abs_nonneg (a i)) ?_
            linarith
          refine (div_le_one₀ ?_).mpr ?_
          exact hS
          have : |a i| + ∑ i ∈ (Icc 1 n).erase i, |a i| = S := by
            simp [S] ;rw [Finset.add_sum_erase (Icc 1 n) (fun i => |a i|) hi]
          rw [← this]
          have : 0 ≤ ∑ i ∈ (Icc 1 n).erase i, |a i| := by
            apply Finset.sum_nonneg
            intro i hi ;exact abs_nonneg (a i)
          linarith
        apply Real.rpow_le_self_of_le_one this.1 this.2 (by norm_num)
      rw [← Finset.sum_div,Real.div_rpow (by linarith) (by linarith)] at this
      have this' : ∑ i ∈ Icc 1 n, (|a i| / S) ^ (5 / 3:ℝ) = ∑ i ∈ Icc 1 n, (|a i|) ^ (5 / 3:ℝ) / (S) ^ (5 / 3:ℝ) := by
        apply sum_congr rfl
        intro x hx
        apply Real.div_rpow (abs_nonneg (a x)) (?_)
        linarith
      rw [this',← Finset.sum_div] at this
      apply (div_le_div_iff_of_pos_right ?_).mp this
      exact Real.rpow_pos_of_pos hS (5 / 3)
    -- so,$$ \sum_{i=1}^{n} a_{i}^{3} \leqslant\left(\sum_{i=1}^{n} a_{i}\right) \cdot\left(\sum_{i=1}^{n} a_{i}^{5}\right)^{2 / 5} $$
    -- which gives $\sum_{i=1}^{n} a_{i} \geqslant \frac{3}{5^{2 / 5}}&gt;\frac{3}{2}$,
    -- since $2^{5}&gt;5^{2}$ and hence $2&gt;5^{2 / 5}$.
    rw [← h1',h1] at h2'
    have : ∑ i ∈ Icc 1 n, |a i ^ (2:ℝ)| ^ (5 / 2:ℝ) = ∑ i ∈ Icc 1 n, a i ^ 5 := by
      apply sum_congr rfl
      intro x hx
      rw [abs_eq_self.mpr (by refine Real.rpow_nonneg (le_of_lt (ha x)) 2),← Real.rpow_mul]
      norm_num
      have : (5:ℝ) = (5:ℕ) := by rfl
      rw [this] ;exact Real.rpow_natCast (a x) 5
      exact le_of_lt (ha x)
    rw [this,h2] at h2' ;norm_num at h2'
    have : (∑ x ∈ Icc 1 n, |a x| ^ (5 / 3:ℝ)) ^ (3 / 5:ℝ) ≤ ((∑ i ∈ Icc 1 n, |a i|)^ (5 / 3 :ℝ)) ^ (3 / 5:ℝ) := by
      refine Real.rpow_le_rpow ?_ h3 (by norm_num)
      apply sum_nonneg
      intro i hi ;refine Real.rpow_nonneg (abs_nonneg (a i)) (5 / 3)
    rw [← Real.rpow_mul] at this ;norm_num at this
    have : (∑ x ∈ Icc 1 n, |a x| ^ (5 / 3 : ℝ)) ^ (3 / 5 : ℝ) * 5 ^ (2 / 5 : ℝ) ≤ (∑ i ∈ Icc 1 n, |a i|) * 5 ^ (2 / 5 : ℝ) := by
      refine mul_le_mul this (by simp) (by refine Real.rpow_nonneg (by norm_num) (2 / 5)) ?_
      apply sum_nonneg ;intro i hi ;exact abs_nonneg (a i)
    have : 3 ≤ (∑ i ∈ Icc 1 n, |a i|) * 5 ^ (2 / 5 : ℝ ) := by linarith
    have this' : ∑ i ∈ Icc 1 n, |a i| = ∑ i ∈ Icc 1 n, a i := by
      apply sum_congr rfl ;exact fun x a_1 ↦ abs_of_pos (ha x)
    rw [this'] at this
    by_contra! h
    have this' : (∑ i ∈ Icc 1 n, a i) * 5 ^ (2 / 5 : ℝ) ≤ 3 / 2 * 5 ^ (2 / 5 : ℝ) := by
      refine mul_le_mul h (by simp) (by refine Real.rpow_nonneg (by norm_num) (2 / 5)) (by norm_num)
    have : (5:ℝ) ^ (2 / 5 : ℝ) < 2 := by
      have : ((5:ℝ)^(2 / 5:ℝ))^(5:ℝ) < 2^(5:ℝ) := by rw [← Real.rpow_mul] ;norm_num ;norm_num
      refine (Real.rpow_lt_rpow_iff ?_ (by norm_num) (by norm_num)).mp this
      refine Real.rpow_nonneg (by norm_num) (2 / 5)
    have : 3 / 2 * (5:ℝ) ^ (2 / 5 : ℝ) < 3 / 2 * 2 := by
      refine (mul_lt_mul_left (by norm_num)).mpr this
    linarith
    apply sum_nonneg ;intro i hi ;exact abs_nonneg (a i)
    