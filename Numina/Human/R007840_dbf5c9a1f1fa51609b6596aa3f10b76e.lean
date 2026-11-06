import Mathlib
open Real Finset BigOperators

/- @hehepig comment:
Given solution provides two approaches.
The first one is difficult to formalize, as it relies on an implicit sequence x.
Therefore, I formalized the second approach (the one in the 'Comment' section of the solution).

By the way, there's no equality condition for AM-GM inequality in the previous version of Mathlib,
And I happen to have written one using Jensen's inequality. (I've recently committed it to the mathlib repo.)
-/

set_option maxHeartbeats 500000
/- Let $a_{2}, \ldots, a_{n}$ be $n-1$ positive real numbers, where $n \geq 3$, such that $a_{2} a_{3} \cdots a_{n}=1$. Prove that  $$ \left(1+a_{2}\right)^{2}\left(1+a_{3}\right)^{3} \cdots\left(1+a_{n}\right)^{n}>n^{n} . $$ -/
theorem imo_a3
    (n : ℕ)
    (a : ℕ → ℝ)
    (h_n : 3 ≤ n)
    (h_apos : ∀ i, a i > 0)
    (h_aprod : ∏ i ∈ Icc 2 n, a i = 1) :
    ∏ i ∈ Icc 2 n, (1 + a i) ^ i > n ^ n := by

  -- aux lemma, equality condition of ge_mul
  have l_0 {a b c d: ℝ} (ha : a ≥ c) (hb : b ≥ d) (hc : c > 0) (hd : d > 0) (h : a * b = c * d) : a = c ∧ b = d := by
    by_contra! h_contra
    by_cases hs : a = c
    . simp_all
    . have : a > c := lt_of_le_of_ne ha fun t => hs t.symm
      have : a * b > c * d := mul_lt_mul_of_pos_of_nonneg' this hb hd (by linarith)
      linarith

  -- aux lemma, eq_of_logeq
  have l_1 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : log a = log b) : a = b := by
    apply_fun exp at hab
    rw [exp_log ha, exp_log hb] at hab
    exact hab

  -- aux lemma, equality condition if AM-GM inequality
  have l_geom_mean_arith_mean_weighted_eq_iff (s : Finset ℕ) (w z : ℕ → ℝ) (hw : ∀ i ∈ s, 0 < w i)
      (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) :
      ∏ i ∈ s, z i ^ w i = ∑ i ∈ s, w i * z i ↔ ∀ j ∈ s, z j = ∑ i ∈ s, w i * z i := by
    by_cases A : ∃ i ∈ s, z i = 0 ∧ w i ≠ 0
    · rcases A with ⟨i, his, hzi, hwi⟩
      rw [prod_eq_zero his]
      · constructor
        · intro h; rw [← h]; intro j hj
          apply eq_zero_of_ne_zero_of_mul_left_eq_zero (ne_of_lt (hw j hj)).symm
          apply (sum_eq_zero_iff_of_nonneg ?_).mp h.symm j hj
          exact fun i hi => (mul_nonneg_iff_of_pos_left (hw i hi)).mpr (hz i hi)
        · intro h
          convert h i his
          exact hzi.symm
      · rw [hzi]
        exact zero_rpow hwi
    · simp only [not_exists, not_and] at A
      have hz' := fun i h => lt_of_le_of_ne (hz i h) (fun a => (A i h a.symm) (ne_of_gt (hw i h)))
      have := strictConvexOn_exp.map_sum_eq_iff hw hw' fun i _ => Set.mem_univ <| log (z i)
      simp only [exp_sum, (· ∘ ·), smul_eq_mul, mul_comm (w _) (log _)] at this
      convert this using 1
      · apply Eq.congr <;> [apply prod_congr rfl; apply sum_congr rfl]
        <;> intro i hi <;> simp [exp_mul, exp_log (hz' i hi)]
      · constructor <;> intro h j hj
        · rw [← arith_mean_weighted_of_constant s w _ (log (z j)) hw' fun i _ => congrFun rfl]
          apply sum_congr rfl
          intro x hx
          simp only [mul_comm, h j hj, h x hx]
        · rw [← arith_mean_weighted_of_constant s w _ (z j) hw' fun i _ => congrFun rfl]
          apply sum_congr rfl
          intro x hx
          simp only [log_injOn_pos (hz' j hj) (hz' x hx), h j hj, h x hx]


  -- Apply the weighted AM-GM inequality to each factor $\left(1+a_{k}\right)^{k}$, with the same weights like above, to obtain  $$ \left(1+a_{k}\right)^{k}=\left((k-1) \frac{1}{k-1}+a_{k}\right)^{k} \geq \frac{k^{k}}{(k-1)^{k-1}} a_{k} $$
  have r1 : ∀ k ∈ Icc 2 n, (1 + a k) ^ k ≥ k ^ k / (k - 1) ^ (k - 1) * a k := by
    intro k hk
    obtain ⟨hk1, _⟩ := mem_Icc.mp hk
    rify at hk1

    -- aux props
    have tt1 : 0 < (k : ℝ) := by linarith
    have tt2 : 0 < (k : ℝ) - 1 := by linarith
    have tt3 : 0 < (k : ℝ) / (k - 1) := div_pos tt1 tt2

    -- use the two-element-amgm theorem in mathlib
    have h_amgm : ((k : ℝ) / (k - 1)) ^ ((k - 1 : ℝ) / k) * ((k * a k)) ^ (1 / (k : ℝ)) ≤ ((k - 1 : ℝ) / k) * ((k : ℝ) / (k - 1)) + (1 / (k : ℝ)) * ((k * a k)) := by
      apply geom_mean_le_arith_mean2_weighted
      any_goals apply le_of_lt; apply div_pos; all_goals linarith
      . apply le_of_lt; apply mul_pos; all_goals linarith [h_apos k]
      . field_simp
    field_simp at h_amgm

    -- do some calculation
    have : (((k : ℝ) / (k - 1)) ^ ((k - 1 : ℝ) / k) * ((k * a k)) ^ (1 / (k : ℝ))) ^ k ≤ (1 + a k) ^ k := by
      apply pow_le_pow_left ?_ h_amgm k
      apply le_of_lt
      apply mul_pos
      . apply rpow_pos_of_pos
        apply div_pos; all_goals linarith
      . apply rpow_pos_of_pos
        apply mul_pos; all_goals linarith [h_apos k]
    apply ge_iff_le.mpr
    convert this using 1
    apply l_1
    . apply mul_pos ?_ (h_apos k)
      apply div_pos; all_goals apply pow_pos; all_goals linarith
    . apply pow_pos
      . apply mul_pos
        . apply rpow_pos_of_pos
          apply div_pos; all_goals linarith
        . apply rpow_pos_of_pos
          apply mul_pos; all_goals linarith [h_apos k]
    rw [log_pow, log_mul _ (ne_of_gt (h_apos k)), log_div (ne_of_gt (pow_pos tt1 k)) (ne_of_gt (pow_pos tt2 _)), log_pow, log_pow, log_mul (ne_of_gt (rpow_pos_of_pos tt3 _)) (ne_of_gt (rpow_pos_of_pos (mul_pos tt1 (h_apos k)) _)), log_rpow tt3, log_rpow (mul_pos tt1 (h_apos k)), log_div (ne_of_gt tt1) (ne_of_gt tt2), log_mul (ne_of_gt tt1) (ne_of_gt (h_apos k)), Nat.cast_sub (by rify; linarith)]
    field_simp; ring_nf
    . apply ne_of_gt
      apply div_pos
      . exact pow_pos tt1 _
      . apply pow_pos tt2 _

  -- aux prop, calculate the prefix product of (1 + a k) ^ k
  have l_2 : ∀ d ≤ (n - 2), ∏ k ∈ Icc 2 (d + 2), (1 + a k) ^ k ≥ (d + 2) ^ (d + 2) * ∏ k ∈ Icc 2 (d + 2), a k := by
    intro d
    induction d with
    | zero =>
      specialize r1 2 (left_mem_Icc.mpr (by linarith))
      norm_num at r1
      norm_num
      exact r1
    | succ d ih =>
      intro hd'
      have hd : d ≤ n - 3 := Nat.sub_le_sub_right hd' 1
      rw [Nat.cast_add, Nat.cast_one, show d + 1 + 2 = d + 2 + 1 by ring_nf, prod_Icc_succ_top (by linarith)]
      specialize r1 (d + 2 + 1) (by simp; omega)
      rw [Nat.cast_add, Nat.cast_add, Nat.cast_one, Nat.cast_two] at r1
      specialize ih (by linarith)
      have := mul_le_mul_of_nonneg ih r1 ?_ ?_
      rw [Nat.add_sub_cancel, show (d : ℝ) + 2 + 1 - 1 = d + 2 by linarith, add_right_comm _ (2:ℝ) 1,
          mul_assoc, mul_comm, mul_assoc, mul_right_comm, div_mul_cancel₀, mul_comm] at this
      apply ge_iff_le.mpr
      convert this using 1
      . rw [mul_assoc, mul_comm (a _), ← prod_Icc_succ_top (by linarith)]
      . apply pow_ne_zero
        linarith
      . apply le_of_lt
        apply mul_pos
        . apply pow_pos
          linarith
        . exact prod_pos fun i _ => h_apos i
      . apply pow_nonneg
        linarith [h_apos (d + 2 + 1)]

  -- Multiplying all these inequalities together gives  $$ \left(1+a_{2}\right)^{2}\left(1+a_{3}\right)^{3} \cdots\left(1+a_{n}\right)^{n} \geq n^{n} a_{2} a_{3} \cdots a_{n}=n^{n} . $$
  have r2 : ∏ k ∈ Icc 2 n, (1 + a k) ^ k ≥ n ^ n := by
    specialize l_2 (n - 2) (Nat.le_refl (n - 2))
    rw [Nat.cast_sub (by linarith), Nat.cast_two, Nat.sub_add_cancel (by linarith), sub_add_cancel, h_aprod, mul_one] at l_2
    exact l_2

  -- The necessary condition for each of the AM-GM equality
  have r3 : ∀ k ∈ Icc 2 n, (1 + a k) ^ k = k ^ k / (k - 1) ^ (k - 1) * a k → a k = (1:ℝ) / (k - 1) := by
    intro k hk h

    obtain ⟨hk1, hk2⟩ := mem_Icc.mp hk

    set w : ℕ → ℝ := fun x => match x with
    | 0 => (k - 1 : ℝ) / k
    | 1 => (1 : ℝ) / k
    | _ => 0

    set z : ℕ → ℝ := fun x => match x with
    | 0 => (k : ℝ) / (k - 1)
    | 1 => k * a k
    | _ => 0

    have t_sum {f : ℕ → ℝ} : ∑ k ∈ Finset.range 2, f k = f 0 + f 1 := by
      simp [show Finset.range 2 = {0, 1} by rfl]

    have t1 : (k : ℝ) ≠ 0 := by norm_cast; linarith
    have t2 : ((k : ℝ) - 1) ≠ 0 := by rify at hk1; linarith

    have hw : ∀ i ∈ range 2, 0 < w i := by
      intro i hi
      rw [mem_range] at hi
      rify at hk1 hk2
      interval_cases i <;> dsimp [w] <;> apply div_pos <;> linarith

    have hw' : ∑ i ∈ range 2, w i = 1 := by
      simp only [t_sum, w, ← add_div, sub_add_cancel, div_self t1]

    have hz : ∀ i ∈ range 2, 0 ≤ z i := by
      intro i hi
      rw [mem_range] at hi
      rify at hk1 hk2
      apply le_of_lt
      interval_cases i
      . dsimp [z]; apply div_pos <;> linarith
      . dsimp [z]; apply mul_pos <;> linarith [h_apos k]

    -- ∏ i ∈ range 2, z i ^ w i = ∑ i ∈ range 2, w i * z i
    have heq : ∏ i ∈ range 2, z i ^ w i = ∑ i ∈ range 2, w i * z i := by
      rify at hk1 hk2
      simp [show Finset.range 2 = {0, 1} by rfl, z, w]
      field_simp
      have tt1 : 0 < (k : ℝ) := by linarith
      have tt2 : 0 < (k : ℝ) - 1 := by linarith
      have tt3 : 0 < (k : ℝ) / (k - 1) := div_pos tt1 tt2
      have tt4 : 0 < (k : ℝ) ^ k := pow_pos tt1 k
      have : log (((k : ℝ) / (k - 1)) ^ (((k : ℝ) - 1) / k) * (k * a k) ^ (1 / (k : ℝ))) = log (1 + a k) := by
        apply_fun fun t : ℝ => log t at h
        rw [log_pow, log_mul _ (ne_of_gt (h_apos k)), log_div (ne_of_gt tt4) (ne_of_gt (pow_pos tt2 _)), log_pow, log_pow, Nat.cast_sub, Nat.cast_one, sub_one_mul] at h
        have : Function.Injective fun t : ℝ => t * k := mul_left_injective₀ t1
        apply_fun fun t : ℝ => t * k
        dsimp
        rw [log_mul, log_rpow tt3, log_div t1 t2, log_rpow, log_mul t1 (ne_of_gt (h_apos k)), add_mul, mul_comm, ← mul_assoc, mul_div, mul_div_cancel_left₀ ((k:ℝ) - 1) t1, mul_right_comm, div_mul_cancel₀ 1 t1, one_mul, sub_one_mul, mul_sub]
        rw [mul_comm _ (k : ℝ), h]
        linarith
        . exact mul_pos tt1 (h_apos k)
        . exact ne_of_gt (rpow_pos_of_pos (div_pos tt1 tt2) _)
        . exact ne_of_gt (rpow_pos_of_pos (mul_pos tt1 (h_apos k)) _)
        . exact Nat.one_le_of_lt (mem_Icc.mp hk).left
        . exact ne_of_gt (div_pos tt4 (pow_pos tt2 _))

      apply l_1 _ _ ?_ ?_ this
      . apply mul_pos ?_ ?_
        . exact rpow_pos_of_pos (div_pos tt1 tt2) _
        . exact rpow_pos_of_pos (mul_pos tt1 (h_apos k)) _
      . trans 1
        . exact Real.zero_lt_one
        . exact lt_add_of_pos_right 1 (h_apos k)

    have h_eqiff := (l_geom_mean_arith_mean_weighted_eq_iff (Finset.range 2) w z hw hw' hz).mp heq
    specialize h_eqiff 1 (self_mem_range_succ 1)
    simp only [t_sum, z, w] at h_eqiff
    apply_fun fun t : ℝ => t / k at h_eqiff
    field_simp at h_eqiff
    field_simp
    linarith

  -- showing that if the equality holds, then all the conditions for equality in the above AM-GM inequalities must be satisfied.
  have r4: ∀ d ≤ n - 2, ∏ k ∈ Icc 2 (d + 2), (1 + a k) ^ k = (d + 2) ^ (d + 2) * ∏ k ∈ Icc 2 (d + 2), a k → ∀ k ∈ Icc 2 (d + 2), a k = (1 : ℝ) / (k - 1) := by
    intro d hd
    induction d with
    | zero =>
      specialize r3 2 (left_mem_Icc.mpr (by linarith))
      norm_num at r3
      norm_num
      exact r3
    | succ d ih =>
      specialize ih (by linarith)
      intro heq
      have hge_n := r1 (d + 2 + 1) (by simp; omega)
      have heqcond_n := r3 (d + 2 + 1) (by simp; omega)
      have hge_prod := l_2 d (by linarith)

      -- aux props
      have t0 : 0 < ((d : ℝ) + 2) ^ (d + 2) := by
        apply pow_pos (by linarith)
      have t1 : 0 < ((d : ℝ) + 2 + 1) ^ (d + 2 + 1) := by
        apply pow_pos (by linarith)

      -- ((d + 2) ^ (d + 2) * ∏ k ∈ Icc 2 (d + 2), a k) * ((d + 2 + 1) ^ (d + 2 + 1) / ((d + 2 + 1) - 1) ^ (d + 2 + 1 - 1) * a (d + 2 + 1)) ≤ (∏ k ∈ Icc 2 (d + 2), (1 + a k) ^ k) * (1 + a (d + 2 + 1)) ^ (d + 2 + 1)
      have hge := mul_le_mul_of_nonneg hge_prod hge_n ?_ ?_
      apply ge_iff_le.mpr at hge
      have ⟨req_prod, req_n⟩ := l_0 hge_prod hge_n ?_ ?_ ?_

      apply heqcond_n at req_n
      apply ih at req_prod
      intro k hk
      rcases eq_or_ne k (d + 2 + 1) with hkv | hkv
      . simp only [hkv, req_n]
      . have : k ∈ Icc 2 (d + 2) := by
          have : 2 ≤ k ∧ k ≤ (d + 2 + 1) := by
            exact (LocallyFiniteOrder.finset_mem_Icc 2 (d + 2 + 1) k).mp hk
          apply mem_Icc.mpr
          constructor
          . linarith
          . obtain ⟨_, th2⟩ := this
            linarith [Nat.lt_of_le_of_ne th2 hkv]
        exact req_prod k this
      any_goals simp only [Nat.cast_add, Nat.cast_one, Nat.cast_two, Nat.add_sub_cancel, show (d : ℝ) + 2 + 1 - 1 = (d : ℝ) + 2 by linarith]

      -- some annoying computation checking
      . exact mul_pos t0 (prod_pos (fun i _ => h_apos i))
      . exact mul_pos (div_pos t1 t0) (by apply h_apos)
      . simp only [Nat.cast_add, Nat.cast_one] at heq
        rw [← prod_Icc_succ_top (by linarith),
            mul_assoc, mul_comm, mul_assoc, mul_right_comm, div_mul_cancel₀ _ (ne_of_lt t0).symm,
            mul_comm, mul_assoc, mul_comm (a _), ← prod_Icc_succ_top (by linarith),
            show (d : ℝ) + 2 + 1 = d + 1 + 2 by apply add_right_comm]
        exact heq
      . exact le_of_lt (mul_pos t0 (prod_pos (fun i _ => h_apos i)))
      . apply le_of_lt
        apply pow_pos
        linarith [h_apos (d + 2 + 1)]

  -- showing that the equality cannot be attained
  have r5 : ∏ k ∈ Icc 2 n, (1 + a k) ^ k ≠ n ^ n := by
    by_contra! h_contra
    specialize r4 (n - 2) (Nat.le_refl (n - 2))
    rw [Nat.cast_sub (by linarith), Nat.cast_two, Nat.sub_add_cancel (by linarith), sub_add_cancel, h_aprod, mul_one] at r4
    apply r4 at h_contra
    have : ∏ i ∈ Icc 2 n, a i ≠ 1 := by
      calc ∏ i ∈ Icc 2 n, a i
        _ = ∏ i ∈ Ico 2 (n + 1), (1 : ℝ) / (i - 1) := by
          exact prod_congr rfl h_contra
        _ = ∏ i ∈ Icc 3 n, (1 : ℝ) / (i - 1):= by
          rw [prod_eq_prod_Ico_succ_bot (by linarith)]
          norm_num
          rfl
        _ ≠ 1 := by
          apply ne_of_lt
          have : ∏ i ∈ Icc 3 n, (1 : ℝ) / (i - 1) < ∏ _ ∈ Icc 3 n, (1 : ℝ) := by
            apply prod_lt_prod ?_ ?_ ?_
            . intro i hi
              rw [mem_Icc] at hi
              rify at hi
              apply div_pos <;> linarith
            . intro i hi
              rw [mem_Icc] at hi
              rify at hi
              rw [← inv_eq_one_div]
              apply inv_le_one_iff.mpr
              right
              linarith
            . use 3
              constructor
              . simp only [mem_Icc, le_refl, true_and, h_n]
              . norm_num
          convert this
          exact prod_const_one.symm
    contradiction

  exact lt_of_le_of_ne r2 r5.symm
