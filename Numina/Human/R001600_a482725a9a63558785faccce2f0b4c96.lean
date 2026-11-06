import Mathlib

open Real Finset Polynomial

/- We show that esymm 1 = a -/
lemma esymm_one_eq_a_of_psum_eq_pow {a : ℝ} {n : ℕ} {x : Fin n → ℝ} (hn : n > 0) (h : ∀ k ∈ Icc 1 n, ∑ i, (x i) ^ k = a ^ k) :
    (univ.val.map x).esymm 1 = a := by
  -- esymm 1 = ∑ i, x i = a.
  rw [←MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin n) ℝ]
  rw [MvPolynomial.esymm_one]
  simp
  obtain h := h 1 (by simp; exact hn)
  simp at h
  exact h

/- If i > n, then esymm i = 0. -/
lemma esymm_eq_zero_of_gt_card {i : ℕ} {R σ : Type*}  [CommSemiring R] [Fintype σ] (hi : i > Fintype.card σ) : MvPolynomial.esymm σ R i = 0 := by
  simp [MvPolynomial.esymm]
  suffices h : powersetCard i (univ : Finset σ) = ∅
  · simp [h]
  · exact powersetCard_eq_empty.mpr hi

lemma esymm_eq_zero_of_psum_eq_pow {a : ℝ} {n : ℕ} {x : Fin n → ℝ} (hn : n > 0) (h : ∀ k ∈ Icc 1 n, (MvPolynomial.psum (Fin n) ℝ k).aeval x = a ^ k) :
    ∀ i, (univ.val.map x).esymm (i + 1 + 1) = 0 := by
  -- First, we have ∑ i, x i = a.
  have h1 : ∑ x_1 : Fin n, x x_1 = a := by
    obtain h := h 1 (by simp; exact hn)
    simp at h
    exact h

  -- We aim to show that for any i, esymm (i + 2) = 0.
  intro i
  rw [←MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin n) ℝ]

  -- Here, we apply the strong induction on i.
  induction i using Nat.strongRec

  -- Assume that for any j < i, esymm (j + 2) = 0.
  rename_i i ih
  simp [add_assoc]

  -- It suffices to show that (i + 2) * esymm (i + 2) = 0.
  have : ((i + 2 : ℕ) * MvPolynomial.esymm (Fin n) ℝ (i + 2)).aeval x = 0 := by
    by_cases hi : n ≥ i + 2
    · -- If n ≥ i + 2, then we can use the Newton's identities.
      -- (i + 2) * esymm (i + 2) = ∑ j < i + 2, (-1) ^ j * (esymm j) * (psum (i + 2 - j)).
      rw [MvPolynomial.mul_esymm_eq_sum (Fin n) ℝ]
      simp
      -- However, ∑ j < i + 2, (-1) ^ j * C (MvPolynomial.esymm (Fin n) ℝ j) * (psum (i + 2 - j)) =
      -- ∑ 1 < j < i + 2, (-1) ^ j * (esymm j) * (psum (i + 2 - j)) + psum (i + 2) - (psum (i + 2)) * esymm 1.
      have : filter (fun a ↦ a.1 < i + 2) (antidiagonal (i + 2)) = filter (fun a ↦ a.1 < i + 2 ∧ a.1 > 1) (antidiagonal (i + 2)) ∪ {(0, i + 2), (1, i + 1)} := by
        ext ⟨x, y⟩
        simp
        constructor <;> intro h
        · obtain ⟨h₁, h₂⟩ := h
          simp [h₁, h₂]
          by_cases hx : x > 1
          · simp [hx]
          · simp at hx
            interval_cases x
            · left
              simp at h₁ ⊢
              exact h₁
            · right; right
              simp
              linarith only [h₁]
        · rcases h with h | h | h
          · simp [h]
          · simp [h]
          · simp [h]
            ring
      rw [this, sum_union]
      · simp
        trans 0 + 0
        · -- For the first part, we have esymm j = 0 for all j < i + 2 and j > 1 according to the induction hypothesis.
          congr
          · apply sum_eq_zero
            intro j hj
            simp at hj ⊢
            left
            have hj' : j.1 = j.1 - 2 + 1 + 1 := by
              simp [add_assoc]
              rw [Nat.sub_add_cancel]
              exact hj.2.2
            rw [hj']
            apply ih
            apply Nat.sub_lt_right_of_lt_add
            · exact hj.2.2
            · exact hj.2.1
          · -- For the second part, we have esymm 1 = a.
            -- Therefore, we have psum (i + 2) - (psum (i + 2)) * esymm 1 = a ^ (i + 2) - a * a ^ (i + 1) = 0.
            rw [h, h, h1]
            · ring
            · simp
              apply le_trans ?_ hi
              simp
            · simp
              exact hi
        · simp
      · simp
    · -- If n < i + 2, then esymm (i + 2) = 0 follows from Lemma esymm_eq_zero_of_gt_card.
      rw [esymm_eq_zero_of_gt_card]
      · simp
      · simp at hi
        simp [hi]
  -- Therefore, the result follows.
  simp at this
  norm_cast at this
  simp at this
  exact this

/- If x satisfies the system of equation and ∃ i, x i = a, then ∀ j ≠ x, x j = 0. -/
lemma eq_zero_of_exists_eq_a {x : Fin n → ℝ} (h : ∀ k ∈ Icc 1 n, ∑ j, (x j) ^ k = a ^ k)
    (i : Fin n) (hi : x i = a) : ∀ j, j ≠ i → x j = 0 := by
  by_cases hn : n ≥ 2
  · -- If n ≥ 2, then we can use the fact that
    -- ∑ j ≠ i, x j ^ 2 = ∑ j, x j ^ 2 - x i ^ 2 = a ^ 2 - a ^ 2 = 0.
    obtain h := h 2 (by simp [hn])
    have : univ = univ.erase i ∪ {i} := by
      rw [union_comm, union_erase_of_mem]
      · simp
      · simp
    rw [this, sum_union, sum_singleton, hi] at h
    · -- Since x j ^ 2 ≥ 0 for all j, we have
      -- x j = 0 for all j ≠ i.
      simp only [add_left_eq_self] at h
      apply sum_eq_zero_iff_of_nonneg (by intro i _; positivity) |>.mp at h
      simp at h
      apply h
    · simp
  · simp at hn
    interval_cases n
    · -- If n = 0, there is nothing to prove.
      simp
    · -- If n = 1, then there is only one variable x 0 = a.
      simp
      fin_cases i
      intro j
      fin_cases j
      simp

/- 7. (CZS 1) Find all real solutions of the system of equations
 $$ \begin{aligned} x_{1}+x_{2}+\cdots+x_{n} & =a, \\ x_{1}^{2}+x_{2}^{2}+\cdots+x_{n}^{2} & =a^{2},
 \\ \ldots \cdots \cdots \cdots+x_{n}^{n} & =a^{n} . \end{aligned} $$ -/
theorem algebra_24753 (n : ℕ) (hn : n > 0) (a : ℝ) :
    {x : Fin n → ℝ | ∀ k ∈ Icc 1 n, ∑ j, (x j) ^ k = a ^ k} = {x : Fin n → ℝ | ∃ i, x i = a ∧ ∀ j, j ≠ i → x j = 0} := by

  ext x
  constructor
  · -- Assume that x satisfies the system of equations.
    intro hx
    let u : Multiset (Fin n) := univ.1
    let s : Multiset ℝ := u.map x
    have hcard_s : s.card = n := by
      simp [s, u]
    have hesymm0 : s.esymm 0 = 1 := by simp [Multiset.esymm]
    have hesymm1 : s.esymm 1 = a := by exact esymm_one_eq_a_of_psum_eq_pow hn hx
    have hesymmi {i : ℕ} : s.esymm (i + 1 + 1) = 0 := by
      apply esymm_eq_zero_of_psum_eq_pow (a := a) hn
      simp [MvPolynomial.psum, MvPolynomial.aeval, -mem_Icc]
      exact hx
    -- Therefore, expand the production, we have
    -- ∏ (X - x i) = ∑ j, (-1) ^ j * C (s.esymm j) * X ^ (n - j) = X ^ n - a * X ^ (n - 1).
    have prod_X_sub_x_i_eq :
        (s.map (fun (t : ℝ) => X - C t)).prod = ∑ j ∈ range (s.card + 1), (-1) ^ j * (C (s.esymm j) * X ^ (s.card - j)) := by
      exact Multiset.prod_X_sub_X_eq_sum_esymm s
    simp [hcard_s] at prod_X_sub_x_i_eq
    simp [sum_range_succ', hesymm0] at prod_X_sub_x_i_eq
    have hn : n = n - 1 + 1 := by
      rw [Nat.sub_add_cancel hn]
    nth_rw 1 [hn] at prod_X_sub_x_i_eq
    simp [sum_range_succ', hesymm1] at prod_X_sub_x_i_eq
    simp [hesymmi] at prod_X_sub_x_i_eq
    -- Therefore, ∏ (a - x i) = a ^ n - a * a ^ (n - 1) = 0.
    apply congrArg (fun p => p.eval a) at prod_X_sub_x_i_eq
    simp [eval_multiset_prod] at prod_X_sub_x_i_eq
    have ha_root : -(a * a ^ (n - 1)) + a ^ n = 0 := by
      nth_rw 2 [hn]
      ring
    -- which implies that ∃ i, a - x i = 0, i.e., ∃ i, x i = a.
    simp [ha_root] at prod_X_sub_x_i_eq
    obtain ⟨xi, hxi, hsub_eq_zero⟩ := prod_X_sub_x_i_eq
    simp [s] at hxi
    obtain ⟨i, _, hxi⟩ := hxi
    rw [←hxi] at hsub_eq_zero
    apply sub_eq_zero.mp at hsub_eq_zero
    use i
    constructor
    · -- Choose this i, we have x i = a
      rw [hsub_eq_zero]
    · -- Then by the lemma, we have ∀ j ≠ i, x j = 0.
      apply eq_zero_of_exists_eq_a (a := a)
      · exact hx
      · simp [hsub_eq_zero]
  · -- Conversely, assume x = (0,..., a, .., 0)
    intro ⟨i, hxi, hj⟩
    intro k hk
    -- Then ∑ j, x j ^ k = ∑ j ≠ i, x j ^ k + x i ^ k = 0 + a ^ k = a ^ k.
    -- Therefore, x is a solution of the system of equations.
    have : univ = univ.erase i ∪ {i} := by
      rw [union_comm, union_erase_of_mem]
      · simp
      · simp
    rw [this, sum_union, sum_singleton]
    · rw [hxi]
      simp only [add_left_eq_self]
      apply sum_eq_zero
      have hk : k ≠ 0 := by
        simp at hk
        obtain hk := hk.1
        exact Nat.not_eq_zero_of_lt hk
      simp [hk]
      exact hj
    · simp
