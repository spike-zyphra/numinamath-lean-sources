import Mathlib

open Real
open scoped BigOperators

/- Example 6 Given that $x_{1}, x_{2}, \cdots, x_{n}$ are pairwise distinct positive integers. Prove that for any positive integer $n$, the inequality
$$
\frac{x_{1}}{1^{2}}+\frac{x_{2}}{2^{2}}+\cdots+\frac{x_{n}}{n^{2}} \geqslant \frac{1}{1}+\frac{1}{2}+\cdots+\frac{1}{n}
$$

holds.
(20th IMO) -/
theorem inequalities_321740 {n : ℕ} (hn : 0 < n) (x : Fin n → ℕ)
  (hx : ∀ i j, x i = x j → i = j) (hx1 : ∀ i, 0 < x i) :
  ∑ i : Fin n, (x i : ℝ)/(i.1 + 1)^2 ≥ ∑ i : Fin n, (1 : ℝ)/(i.1 + 1) := by

  -- Introduce parameters α_1, …, α_n
  -- let 1/1 = 1/x_1 + α_1, …, 1/n = 1/x_n + α_1
  let α : Fin n → ℝ := fun i ↦ (1 : ℝ) / (i.1 + 1) - 1 / x i

  -- the following lemmas are for proving ∑ i, α_i ≥ 0.
  -- lemma 1 : There exists an index k such that x_k ≥ n.
  -- this follows from the fact that x_1, …, x_n are pairwise distinct positive integers.
  have lem_exists_ge_n {n : ℕ} (hn : 0 < n) (x : Fin n → ℕ)
    (hx : ∀ i j, x i = x j → i = j) (hx1 : ∀ i, 0 < x i) :
    ∃ k, x k ≥ n := by
      by_contra! h_x_lt

      let T : Finset ℕ := Finset.Ico 1 n
      have hT_card : T.card = n - 1 := by unfold T; apply Nat.card_Ico

      let S : Finset (Fin n) := .univ
      have hS_card : S.card = n := by simp only [Finset.card_univ, Fintype.card_fin, S]

      have hx' : ∀ i ∈ S, x i ∈ T := by
        intro i _
        simp [T]
        use hx1 i
        use h_x_lt i

      have h_card_le : T.card * 1 < S.card := by
        rw [hT_card, hS_card, mul_one]
        exact Nat.sub_one_lt_of_lt hn

      have ⟨y, ymem, hy⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hx' h_card_le

      apply Finset.one_lt_card.mp at hy
      simp at hy
      obtain ⟨a, amem_xa, b, bmem_xb, aneb⟩:= hy
      have : x a = x b := by
        trans y
        exact amem_xa.2
        exact bmem_xb.2.symm
      have := hx a b this
      contradiction

  -- lemma 2 : ∑ i : Fin (n + 1), f i = ∑ i : Fin n, f i + f n
  -- this is needed for induction
  have lem_sum_fin_succ {n : ℕ} {f : Fin (n + 1) → ℝ} :
    ∑ i : Fin (n + 1), f i = ∑ i : Fin n, f i + f n := by
      nth_rw 1 2 [Finset.sum_fin_eq_sum_range]
      rw [Finset.sum_range_succ]
      congr 1
      · rw [Finset.sum_fin_eq_sum_range]
        apply Finset.sum_congr rfl
        intro x hx
        have : x < n := by exact List.mem_range.mp hx
        simp [this, show x < n + 1 by exact Nat.lt_add_right 1 this]
        congr
        refine Eq.symm (Nat.mod_eq_of_lt ?_)
        exact Nat.lt_add_right 1 this
      · simp
        congr

  -- lemma 3 : ∑_i=1^n, 1/i ≥ ∑ i, i / x_i
  -- we prove this by induction on n.
  -- for induction step, we swap the element x_k where x_k ≥ n + 1 with the last element x_n+1
  have lem_sum_n_le {n : ℕ} (hn : 0 < n) (x : Fin n → ℕ)
    (hx : ∀ i j, x i = x j → i = j) (hx1 : ∀ i, 0 < x i) :
    ∑ i : Fin n, (1 : ℝ) / (i.1 + 1) ≥ ∑ i : Fin n, (1 : ℝ) / x i := by

    induction n, hn using Nat.le_induction
    case base =>
      simp
      exact Nat.cast_inv_le_one (x 0)

    case succ n hn ih =>
      have ⟨i₀, hi₀⟩ := lem_exists_ge_n (show n + 1 > 0 by exact Nat.add_pos_left hn 1) x hx hx1
      let x' : Fin n → ℕ := fun i ↦ if i = i₀ then x n else x i

      have h_x_i₀ : (1 : ℝ) / (x i₀) ≤ 1 / (n + 1) := by
        refine one_div_le_one_div_of_le ?_ ?_
        · norm_cast; exact Nat.add_pos_left hn 1
        norm_cast

      have : ∑ i : Fin (n + 1), (1 : ℝ) / (x i) = ∑ i : Fin n, (1 : ℝ) / (x' i) + (1 : ℝ) / (x i₀) := by
        let x'' : Fin (n + 1) → ℕ := fun i ↦ if i = i₀ then x n else (if i = n then x i₀ else x i)

        have h_x'_x'' : ∀ i : Fin n, x' i = x'' i := by
          intro i
          by_cases hi : i.castSucc = i₀
          · simp [x', x'', hi]
          have : i.castSucc ≠ Fin.last n := by
            intro hi_eq
            have : i = n := by
              trans i.castSucc.val
              · rfl
              simp [hi_eq]
            have : i < n := by exact i.isLt
            linarith
          simp [x', x'', hi, this]

        have : ∑ i : Fin n, (1 : ℝ) / (x' i) = ∑ i : Fin n, (1 : ℝ) / (x'' i) := by
          congr; ext i; congr
          exact h_x'_x'' i
        rw [this]

        have : (1 : ℝ) / (x i₀) = 1 / x'' n := by
          congr
          by_cases hi : i₀ = n
          · simp [x'', hi]
          have : i₀ ≠ Fin.last n := by
            intro heq
            rw [heq] at hi
            simp at hi
          simp [x'', this.symm]
        rw [this]

        rw [← lem_sum_fin_succ (f := fun i ↦ (1 : ℝ) / (x'' i))]

        let e := (fun (i : Fin (n + 1)) ↦ if i = i₀ then Fin.last n else (if i = n then i₀ else i))
        apply Fintype.sum_bijective e
        · apply Fintype.bijective_iff_surjective_and_card e |>.mpr
          constructor
          · intro b
            by_cases hb_i₀ : b = i₀
            · use Fin.last n
              simp [e]
              by_cases hi₀_n : Fin.last n = i₀
              all_goals simp [e, hi₀_n, hb_i₀]
            by_cases hb_n : b = Fin.last n
            · use i₀
              simp [e, hb_n]
            use b
            simp [e, hb_n, hb_i₀]
          rfl
        · intro i
          congr
          by_cases hi_i₀ : i = i₀
          all_goals by_cases hi_n : Fin.last n = i
          · simp [e, x'', hi_i₀, hi_n]
          · simp [x'', hi_i₀, hi_n]
            by_cases hi₀_n : Fin.last n = i₀
            all_goals simp [e, hi₀_n]
          · simp [e, x'', hi_i₀, hi_n]
          · push_neg at hi_n; simp [e, hi_i₀, hi_n.symm, x'']
      rw [this]

      rw [lem_sum_fin_succ]
      apply add_le_add
      · have := ih x' ?_ ?_
        norm_cast at this ⊢
        · intro i j heq
          unfold x' at heq
          by_cases hi : i = i₀
          all_goals by_cases hj : j = i₀
          · refine Fin.eq_of_val_eq ?_
            simp at hi hj
            have : i.castSucc = j.castSucc := by
              trans i₀
              assumption
              exact hj.symm
            exact
              Fin.mk.inj_iff.mp
                (hx ⟨↑i, Fin.castLE.proof_1 (Nat.le_add_right n 1) i⟩
                  ⟨↑j, Fin.castLE.proof_1 (Nat.le_add_right n 1) j⟩
                  (congrArg x
                    (hx ⟨↑i, Fin.castLE.proof_1 (Nat.le_add_right n 1) i⟩
                      ⟨↑j, Fin.castLE.proof_1 (Nat.le_add_right n 1) j⟩ (congrArg x this))))
          all_goals
            norm_cast at *
            simp [hi, hj] at heq
          · have := hx (Fin.last n) j.castSucc heq
            simp at this
            have : n = j := Fin.mk.inj_iff.mp
                (hx ⟨n, Nat.lt_succ_self n⟩ ⟨↑j, Fin.castLE.proof_1 (Nat.le_add_right n 1) j⟩ heq)
            have : j < n := by exact j.isLt
            linarith
          · have := hx i.castSucc (Fin.last n) heq
            simp at this
            have : n = i := Fin.mk.inj_iff.mp
                (hx ⟨n, Nat.lt_succ_self n⟩ ⟨↑i, Fin.castLE.proof_1 (Nat.le_add_right n 1) i⟩
                  (id (Eq.symm heq)))
            have : i < n := by exact i.isLt
            linarith
          · have := hx i.castSucc j.castSucc heq
            exact Fin.castSucc_inj.mp (hx i.castSucc j.castSucc heq)
        · intro i
          unfold x'
          by_cases hi : i = i₀
          · simp [hi]
            exact hx1 (Fin.last n)
          · simp [hi]
            exact ite_pos (hx1 (Fin.last n)) (hx1 i.castSucc)
      · refine one_div_le_one_div_of_le ?_ ?_
        norm_cast; apply Nat.zero_lt_succ
        simp
        norm_cast

  -- now it follows from the previous lemma that ∑ i, α_i ≥ 0.
  have h_α_sum_nonneg : ∑ i : Fin n, α i ≥ 0 := by
    unfold α
    rw [Finset.sum_sub_distrib]
    apply sub_nonneg.mpr
    exact lem_sum_n_le hn x hx hx1

  -- we start to transform the LHS
  -- 1. ∑ i, x_i / i^2 = ∑ i, x_i * (1/i)^2
  have : ∑ i : Fin n, (x i : ℝ) / (i.1 + 1) ^ 2 =
    ∑ i : Fin n, (x i : ℝ) * (1 / (i.1 + 1)) ^ 2 := by
      congr
      ext i
      field_simp
  rw [this]

  -- 2. recall that 1 / i = (1 / x_i) + α_i
  -- so ... = ∑ i, x_i * ((1 / x_i) + α_i)^2
  have : ∑ i : Fin n, (x i : ℝ) * (1 / (i.1 + 1)) ^ 2 =
    ∑ i : Fin n, (x i : ℝ) * (1 / (x i) + α i) ^ 2 := by
      congr
      ext i
      congr
      simp [α]
  rw [this]

  -- expand the square, we get ... = ∑ i, (1 / x_i + 2α_i * x_iα_i^2)
  have : ∑ i : Fin n, (x i : ℝ) * (1 / (x i) + α i) ^ 2 =
    ∑ i : Fin n, ((1 : ℝ) / x i + 2 * α i + x i * α i ^ 2) := by
      congr
      ext i
      rw [add_pow_two, mul_add, mul_add]
      congr 1
      congr 1
      · rw [pow_two]; field_simp
      · rw [mul_assoc, ← mul_assoc, ← mul_assoc]
        field_simp [show (x i : ℝ) ≠ (0 : ℝ) by norm_cast; exact Nat.not_eq_zero_of_lt (hx1 i)]
  rw [this]

  -- reform it to ... = ∑ i, (1 / x_i + α_i)  +  ∑ i, α_i  +  ∑ i, x_iα_i^2
  have : ∑ i : Fin n, ((1 : ℝ) / x i + 2 * α i + x i * α i ^ 2) =
    ∑ i : Fin n, (((1 : ℝ) / x i + α i) + α i + x i * α i ^ 2) := by
      congr
      ext i
      ring
  rw [this]

  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

  -- the first summation is exactly ∑ i, 1 / i by definition of α_i
  have : ∑ i : Fin n, ((1 : ℝ) / (x i) + α i) = ∑ i : Fin n, (1 : ℝ) / (i.1 + 1) := by
    congr
    ext i
    field_simp [α]
  rw [this]

  rw [add_assoc]
  simp

  -- the other two summations are clearly nonnegative, we are done.
  positivity
