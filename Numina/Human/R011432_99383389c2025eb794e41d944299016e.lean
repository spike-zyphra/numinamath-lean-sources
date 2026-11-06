import Mathlib

open Real

/- 10. (SWE 4) ${ }^{\mathrm{IMO} 3}$ Let $1=a_{0} \leq a_{1} \leq a_{2} \leq \cdots \leq a_{n} \leq \cdots$ be a sequence of real numbers. Consider the sequence $b_{1}, b_{2}, \ldots$ defined by:  $$ b_{n}=\sum_{k=1}^{n}\left(1-\frac{a_{k-1}}{a_{k}}\right) \frac{1}{\sqrt{a_{k}}} $$  Prove that: (a) For all natural numbers $n, 0 \leq b_{n}<2$. (b) Given an arbitrary $0 \leq b<2$, there is a sequence $a_{0}, a_{1}, \ldots, a_{n}, \ldots$ of the above type such that $b_{n}>b$ is true for infinitely many natural numbers $n$. -/
theorem algebra_24849 (a : ℕ → ℝ) (ha : Monotone a) (ha₀ : a 0 = 1)
    (b : ℕ → ℝ) (hb : ∀ n ≥ 1, b n = ∑ k ∈ Finset.Icc 1 n, ((1 - a (k - 1) / a k) / √(a k))) :
    (∀ n ≥ 1, 0 ≤ b n ∧ b n < 2) ∧
    (∀ b₀, 0 ≤ b₀ ∧ b₀ < 2 →
      ∃ (a' b' : ℕ → ℝ), Monotone a' ∧ (a' 0 = 1) ∧ (∀ n ≥ 1, b' n = ∑ k ∈ Finset.Icc 1 n, ((1 - a' (k - 1) / a' k) / √(a' k))) ∧
      {n : ℕ | n ≥ 1 ∧ b' n > b₀}.Infinite) := by
  constructor
  · -- According to the hypothesis, we have a_i > 0 for all i.
    intro n hn
    rw [hb n hn]
    have ha_pos {n : ℕ} : a n > 0 := by
      induction n with
      | zero => simp [ha₀]
      | succ n ih =>
        apply lt_of_lt_of_le ih
        apply ha
        simp
    constructor
    · -- therefore, b_n > 0 is trivial.
      apply Finset.sum_nonneg
      intro i _
      apply div_nonneg
      · have : a i > 0 := by apply ha_pos
        field_simp
        apply div_nonneg
        · simp
          apply ha
          simp
        · apply le_of_lt this
      · positivity
    · -- Then we prove that (1 - a (k - 1) / a k) / √(a k) ≤ 2 * (1 / √(a (k -1)) - 1 / √(a k))  for all k ≥ 1
      apply lt_of_le_of_lt (b := 2 * (1 / √(a 0) - 1 / √(a n)))
      · trans 2 * ∑ k ∈ Finset.Icc 1 n, (1 / √(a (k - 1)) - 1 / √(a k))
        · rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro i _
          apply sub_nonneg.mp
          have : a i > 0 := by apply ha_pos
          have : a (i - 1) > 0 := by apply ha_pos
          field_simp
          apply div_nonneg
          · ring_nf
            rw [sq_sqrt]
            · trans √(a i) * (√(a i) - √(a (i - 1))) ^ 2 * (2 * √(a i) + √(a (i - 1)))
              · positivity
              · apply le_of_eq
                apply sub_eq_zero.mp
                ring_nf
                have {r : ℝ} (hr : r ≥ 0) : √r ^ 3 = r * √r := by
                  rw [show 3 = 2 + 1 by rfl, pow_add]
                  rw [sq_sqrt hr]
                  ring
                rw [this, this]
                ring_nf
                rw [show 4 = 2 + 2 by rfl, pow_add, sq_sqrt]
                ring
                all_goals positivity
            · positivity
          · positivity
        · -- Summing up the above inequality, we have b_k ≤ 2 * (1 / √(a_0) - 1 / √(a k)) = 2 - 2 / √(a k) < 2
          apply mul_le_mul_of_nonneg_left
          · rw [Finset.sum_sub_distrib]
            nth_rw 1 [Finset.Icc_eq_cons_Ioc, Finset.sum_cons]
            rw [Finset.Icc_eq_cons_Ico, Finset.sum_cons]
            norm_num
            apply sub_nonneg.mp
            ring_nf
            simp
            apply le_of_eq
            have : Finset.Ioc 1 n = (Finset.Ico 1 n).image (fun i => i + 1) := by
              ext x
              simp
              constructor <;> intro ⟨h₁, h₂⟩
              · constructor
                · exact h₁
                · exact Order.lt_add_one_iff.mpr h₂
              · constructor
                · exact h₁
                · exact Nat.le_of_lt_succ h₂
            rw [this, Finset.sum_image]
            · simp
            · intro x _ y _ h
              simp at h
              exact h
            all_goals exact hn
          · positivity
      · apply lt_of_lt_of_eq (b := 2 / √(a 0))
        · apply sub_pos.mp
          ring_nf
          apply mul_pos
          · simp
            apply ha_pos
          · simp
        · simp [ha₀]
  · -- Given b₀ < 2, let q = 3 / (b₀ + 1) > 1. We define a' and b' as follows:
    --   a'_n = q^n, b'_n = (√q + 1) / q * (1 - q^(-n / 2))
    intro b₀ ⟨hb₀_ge, hb₀_lt⟩
    let q : ℝ := 3 / (b₀ + 1)
    have hq : q > 1 := by
      unfold q
      apply sub_pos.mp
      field_simp
      apply lt_of_lt_of_eq (b := 2 + 1)
      · gcongr
      · norm_num
    -- It is easy to see that a' is monotone and a'_0 = 1.
    let a' : ℕ → ℝ := fun n => q ^ n
    have ha' : Monotone a' := by
      unfold a'
      refine pow_right_mono₀ ?_
      exact le_of_lt hq
    have ha₀' : a' 0 = 1 := by
      unfold a'
      simp
    -- Also, we can see that a' b' are two sequences of the above type.
    let b' : ℕ → ℝ := fun n => ∑ k ∈ Finset.Icc 1 n, (1 - a' (k - 1) / a' k) / √(a' k)
    use a', b', ha', ha₀'
    constructor
    · intro _ _
      unfold b'
      rfl
    · have hb' {n : ℕ} : b' n = (√q + 1) / q * (1 - q ^ (- n / 2 : ℝ)) := by
        induction n with
        | zero => simp [b']
        | succ n ih =>
          unfold b'
          rw [Finset.Icc_eq_cons_Ico, Finset.sum_cons]
          rw [←Nat.Icc_pred_right, Nat.add_sub_cancel]
          unfold b' at ih
          rw [ih]
          unfold a'
          · have {q : ℝ} (hq : q > 1) : (1 - q ^ n / q ^ (n + 1)) / √(q ^ (n + 1)) = (√q + 1) / q * ((√q - 1) * q ^ (- n / 2 : ℝ) / √q) := by
              field_simp
              apply sub_eq_zero.mp
              ring_nf
              rw [sqrt_eq_rpow, sqrt_eq_rpow, ←rpow_natCast, mul_rpow, ←rpow_mul, ←rpow_add, mul_assoc, ←rpow_add, ←rpow_natCast, ←rpow_mul, mul_assoc, ←rpow_add, mul_assoc, ←rpow_add, mul_assoc, ←rpow_add, mul_assoc, ←rpow_add, mul_assoc, ←rpow_add, mul_assoc, ←rpow_add, ←rpow_natCast, ←rpow_add]
              ring_nf
              nth_rw 1 [←rpow_one q, ←rpow_add]
              ring_nf
              all_goals positivity
            rw [this hq, ←mul_add]
            congr 1
            rw [sub_mul, sub_div, mul_div_cancel_left₀, one_mul]
            rw [Nat.cast_add, neg_add, add_div, rpow_add]
            apply sub_eq_zero.mp
            simp
            apply sub_eq_zero.mpr
            rw [div_eq_mul_inv _ √q]
            congr 1
            rw [sqrt_eq_rpow, neg_div, rpow_neg]
            all_goals positivity
          · simp
          · simp
      -- Observe that b' is also strictly increasing.
      -- let N = 1 + ⌈-2 * log_q (1 - b₀ * q / (√q + 1))⌉
      -- We prove that if n ≥ N, then b'_n > b₀.
      let N : ℕ := 1 + Nat.ceil (- 2 * logb q (1 - b₀ * q / (√q + 1)))
      have hN_le : 1 - q ^ (-N / 2 : ℝ) > b₀ * q / (√q + 1) := by
        have : N > (-2) * logb q (1 - b₀ * q / (√q + 1)) := by
          simp [N]
          apply lt_of_le_of_lt (b := (Nat.ceil (- 2 * logb q (1 - b₀ * q / (√q + 1))) : ℝ))
          · simp
            exact Nat.le_ceil (-(2 * logb q (1 - b₀ * q / (√q + 1))))
          · simp
        have : -N / 2 < logb q (1 - b₀ * q / (√q + 1)) := by
          apply sub_pos.mp
          field_simp
          apply sub_pos.mpr at this
          field_simp at this
          apply lt_of_lt_of_eq this
          ring
        have : q ^ (-N / 2 : ℝ) < 1 - b₀ * q / (√q + 1) := by
          apply lt_of_lt_of_eq (b := q ^ (logb q (1 - b₀ * q / (√q + 1))))
          · apply rpow_lt_rpow_left_iff hq |>.mpr this
          · rw [rpow_logb]
            · positivity
            · apply ne_of_gt hq
            · field_simp
              trans 2
              · simp [q]
                apply sub_pos.mp
                field_simp
                apply sub_pos.mp
                ring_nf
                simp [hb₀_lt]
              · have : √q > 1 := by
                  apply lt_sqrt_of_sq_lt
                  simp [hq]
                linarith only [this]
        exact lt_tsub_comm.mp this
      have hN_ge : N ≥ 1 := by simp [N]
      have hN (n : ℕ) (hn : n ≥ N) : b' n > b₀ := by
        rw [hb']
        apply lt_of_lt_of_le (b := (√q + 1) / q * (1 - q ^ (-N / 2 : ℝ)))
        · apply sub_pos.mp
          field_simp
          apply sub_pos.mpr at hN_le
          field_simp at hN_le
          rw [mul_comm] at hN_le
          apply lt_of_lt_of_eq hN_le
          rw [mul_comm]
        · gcongr
          apply le_of_lt hq
      -- Therefore, b_n > b₀ is true for infinitely many n (≥ N).
      have : Set.Ici N ⊆ {n | n ≥ 1 ∧ b' n > b₀} := by
        intro n hn
        simp at hn ⊢
        constructor
        · apply le_trans hN_ge hn
        · apply hN
          exact hn
      apply Set.Infinite.mono this
      exact Set.Ici_infinite N
