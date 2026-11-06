import Mathlib

open Real Set
open scoped BigOperators

/- Let $a_{1}, a_{2}, \ldots, a_{n}$ be a sequence of $n>3$ real numbers such that  $$ a_{1}+\cdots+a_{n} \geq n \quad \text { and } \quad a_{1}^{2}+\cdots+a_{n}^{2} \geq n^{2} $$  Prove that $\max \left(a_{1}, \ldots, a_{n}\right) \geq 2$. -/
theorem inequalities_606227 {n : ℕ} (hn : n > 3) (a : Fin n → ℝ)
    (hsum : ∑ i, a i ≥ n) (hsumsq : ∑ i, (a i) ^ 2 ≥ n ^ 2) :
    Finset.max (Finset.univ.image a) ≥ 2 := by

  match h : (Finset.image a Finset.univ).max with
  | ⊥ =>
    -- (Finset.univ.image a) is not empty
    apply Finset.max_eq_bot.mp at h
    simp at h
    apply Finset.univ_eq_empty_iff.mp at h
    have : ¬ IsEmpty (Fin n) := by
      simp
      refine Fin.pos_iff_nonempty.mp ?_
      exact Nat.zero_lt_of_lt hn
    contradiction
  | some b =>
    -- by contradition, assum that max a < 2
    have (i : Fin n) : a i ≤ b := by
      have : a i ∈ Finset.univ.image a := by simp
      apply Finset.le_max_of_eq this
      exact h
    by_contra h
    simp at h
    -- then ∀ i, ai < 2
    have hlt (i : Fin n) : a i < 2 := by
      apply lt_of_le_of_lt (this i)
      exact WithBot.coe_lt_coe.mp h
    -- split the sum into positive and negative parts
    let S := Finset.filter (λ i => a i ≥ 0) Finset.univ
    let T := Finset.filter (λ i => a i < 0) Finset.univ
    have hunion : S ∪ T = Finset.univ := by
      ext i
      simp [S, T]
      by_cases h : a i ≥ 0
      · simp [h]
      · simp at h
        simp [h]
    have hsumsq' := hsumsq
    rw [←hunion] at hsum hsumsq
    have hdisj : Disjoint S T := by
      intro x hx1 hx2 i hi
      obtain h1 := hx1 hi
      obtain h2 := hx2 hi
      simp [S] at h1
      simp [T] at h2
      linarith
    rw [Finset.sum_union hdisj] at hsum hsumsq
    -- the positive part S is nonempty
    have hS : S.Nonempty := by
      by_contra h
      simp at h
      simp [h] at hsum
      have : n ≤ (0 : ℝ) := by
        apply le_trans hsum
        apply Finset.sum_nonpos
        intro i hi
        simp [T] at hi
        exact le_of_lt hi
      norm_cast at this
      linarith
    -- the sum of the negative part T is bounded by 2|S| - n
    have hsum : ∑ x ∈ T, |a x| < 2 * S.card - n := by
      calc
        ∑ x ∈ T, |a x| = ∑ x ∈ T, - a x := by
          apply Finset.sum_congr rfl
          intro x hx
          simp [T] at hx
          exact abs_of_neg hx
        _ = - ∑ x ∈ T, a x := by simp
        _ ≤ ∑ x ∈ S, a x - n := by simp; exact hsum
        _ < ∑ x ∈ S, 2 - n := by
          simp only [sub_lt_sub_iff_right]
          apply Finset.sum_lt_sum
          · intro i _
            exact le_of_lt (hlt i)
          · obtain ⟨x, hx⟩ := hS
            use x, hx
            exact hlt x
        _ = 2 * S.card - n := by simp; ring
    -- then n ^ 2 ≤ ∑ ai ^ 2 = ∑_S ai ^ 2 + ∑_T ai ^ 2 < 4|S| + (∑_T |ai|) ^ 2 < 4|S| + (2|S| - n) ^ 2 = 4|S| * (1 + |S| - n) + n ^ 2
    have hsumsq : (n : ℝ) ^ 2 < 4 * S.card * (1 + S.card - n) + n ^ 2 := by
      calc
        (n : ℝ) ^ 2 ≤ ∑ x ∈ S, a x ^ 2 + ∑ x ∈ T, a x ^ 2 := by exact hsumsq
        _ = ∑ x ∈ S, a x ^ 2 + ∑ x ∈ T, |a x| ^ 2 := by
          rw [add_right_inj]
          apply Finset.sum_congr rfl
          intro x _
          simp
        _ < ∑ x ∈ S, 2 ^ 2 + ∑ x ∈ T, |a x| ^ 2 := by
          apply add_lt_add_right
          apply Finset.sum_lt_sum
          · intro i hi
            apply pow_le_pow_left₀
            · simp [S] at hi; exact hi
            · apply le_of_lt (hlt i)
          · obtain ⟨x, hx⟩ := hS
            use x, hx
            apply pow_lt_pow_left₀
            · exact hlt x
            · simp [S] at hx; exact hx
            · norm_num
        _ = 4 * S.card + ∑ x ∈ T, |a x| ^ 2 := by
          rw [add_left_inj]
          norm_num
          ring
        _ ≤ 4 * S.card + (∑ x ∈ T, |a x|) ^ 2 := by
          apply add_le_add_left
          apply Finset.sum_sq_le_sq_sum_of_nonneg
          intro i _
          exact abs_nonneg (a i)
        _ < 4 * S.card + (2 * S.card - n) ^ 2 := by rel [hsum]
        _ = 4 * S.card * (1 + S.card - n) + n ^ 2 := by ring
    -- then 0 < 4 * S.card * (1 + S.card - n)
    simp at hsumsq
    apply mul_pos_iff.mp at hsumsq
    rcases hsumsq with h1 | h2
    · -- if 1 + S.card - n ≤ 0
      obtain h1 := h1.right
      simp at h1
      norm_cast at h1
      have : S = Finset.univ := by
        apply Finset.eq_of_subset_of_card_le
        · simp [S]
        · simp
          exact Nat.lt_one_add_iff.mp h1
      simp [this] at hsumsq'
      -- then n ^ 2 = ∑ ai ^ 2 < 4 * n, which implies n < 4
      have : (n : ℝ) ^ 2 < 4 * n := by
        calc
          (n : ℝ) ^ 2 ≤ ∑ i, (a i) ^ 2 := by exact hsumsq'
          _ < ∑ i, 2 ^ 2 := by
            apply Finset.sum_lt_sum
            · intro i hi
              apply pow_le_pow_left₀
              · rw [←this] at hi
                simp [S] at hi
                exact hi
              · exact le_of_lt (hlt i)
            · obtain ⟨x, hx⟩ := hS
              use x
              simp
              apply pow_lt_pow_left₀
              · exact hlt x
              · simp [S] at hx
                exact hx
              · norm_num
          _ = 4 * n := by simp; norm_num; rw [mul_comm]
      have : (n : ℝ) * (n - 4) < 0 := by rw [mul_sub, ←sq, mul_comm]; simp [this]
      apply mul_neg_iff.mp at this
      simp at this
      norm_cast at this
      simp at this
      obtain h := this.right
      -- since n > 3, contradiction
      have : ¬ n < 4 := by push_neg; exact hn
      contradiction
    · -- if 4 * S.card < 0, contradiction
      obtain h := h2.left
      norm_cast at h
