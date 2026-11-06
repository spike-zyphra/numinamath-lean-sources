import Mathlib

/- if n^2 ≤ i < (n+1)^2, then Nat.sqrt i = n.  -/
lemma l_nat_sqrt_eq_of_mem_Icc {i n:ℕ}
  (hi: i ∈ Finset.Icc (n^2) ((n+1)^2-1)):
  Nat.sqrt i = n := by
  simp only [Finset.mem_Icc] at hi
  apply le_antisymm
  · suffices i.sqrt < n+1 by
      exact Nat.le_of_lt_succ this
    rw [Nat.sqrt_lt]
    have: (n+1)*(n+1) = (n+1)^2-1 + 1 := by
      simp only [pow_two, one_le_mul_self_iff,
      le_add_iff_nonneg_left, zero_le, Nat.sub_add_cancel]
    rw [this]
    exact Order.lt_add_one_iff.mpr hi.right
  · rw [Nat.le_sqrt, ← pow_two]
    exact hi.left


/- Let $M$ be a positive integer. Evaluate the sum
$$ \sum_{k=1}^{M} \frac{1}{2\lfloor\sqrt{k}\rfloor+1} . $$
Show that this value is equal to $\lfloor\sqrt{M}\rfloor - 1 + \frac{M - \lfloor\sqrt{M}\rfloor^2 + 1}{2\lfloor\sqrt{M}\rfloor+1}$.  -/
theorem number_theory_640661 (M : ℕ) (hM : 0 < M) :
    ∑ k ∈ Finset.Icc 1 M, (1 / (2 * ⌊√k⌋₊ + 1 : ℝ)) =
    ⌊√M⌋ - 1 + (M - ⌊√M⌋₊ ^ 2 + 1) / (2 * ⌊√M⌋₊ + 1 : ℝ) := by

  -- consider sum from n^2 to (n+1)^2-1
  -- here 1 / (2 √i + 1) is always 1/(2n+1), and sum becomes 1.
  have h1 {n:ℕ}: ∑ i ∈ Finset.Icc (n^2) ((n+1)^2-1),
    (1 / (2 * ⌊√i⌋₊ + 1: ℝ)) = 1 := by
    have h1: ∀i ∈ Finset.Icc (n^2) ((n+1)^2-1),
      (1 / (2 * ⌊√i⌋₊ + 1: ℝ)) = 1 / (2*n+1: ℝ) := by
      intro i hi
      congr 3
      rw [Real.nat_floor_real_sqrt_eq_nat_sqrt]
      simp only [l_nat_sqrt_eq_of_mem_Icc hi]
    have h2: (Finset.Icc (n^2) ((n+1)^2-1)).card = 2*n+1 := by
      simp only [Nat.card_Icc]
      have: 1 ≤ (n+1)^2 := Nat.one_le_pow _ _ (by simp)
      rw [Nat.sub_add_cancel this, Nat.sq_sub_sq]
      simp only [add_tsub_cancel_left, mul_one]
      ring
    rw [Finset.sum_congr rfl h1, Finset.sum_const, h2]
    suffices 2*n+1 ≠ 0 by
      rify at this
      simp [this]
    simp

  -- consider sum from 1 to n^2-1, it is n-1.
  have h2 {n:ℕ} (hn: 0 < n):
    ∑ i ∈ Finset.Icc 1 (n^2-1: ℕ),
      (1 / (2 * ⌊√i⌋₊ + 1 : ℝ)) = n - 1 := by
    induction' n,hn using Nat.le_induction with n hn ih
    · simp
    · have hh1: Finset.Icc 1 ((n+1)^2 - 1) =
        Finset.Ico 1 ((n+1)^2 - 1+1) := rfl
      have hh2: Finset.Icc 1 (n^2-1) =
        Finset.Ico 1 (n^2-1+1) := rfl
      have hh3: Finset.Icc (n^2) ((n+1)^2-1) =
        Finset.Ico (n^2) ((n+1)^2 - 1+1) := rfl
      have: Finset.Icc 1 ((n+1)^2 - 1) =
        (Finset.Icc 1 (n^2-1)) ∪ (Finset.Icc (n^2) ((n+1)^2-1)) := by
        have: 1 ≤ n^2 := Nat.one_le_pow _ _ hn
        rw [Nat.sub_add_cancel this] at hh2
        rw [hh1, hh2, hh3, Finset.Ico_union_Ico_eq_Ico this]
        suffices 1 ≤ (n+1)^2 by
          rw [Nat.sub_add_cancel this]
          apply Nat.pow_le_pow_left (by simp)
        apply Nat.one_le_pow _ _ (by simp)
      have hh: Disjoint (Finset.Icc 1 (n^2-1))
        (Finset.Icc (n^2) ((n+1)^2-1)) := by
        rw [hh2, hh3]
        nth_rw 1 [Nat.sub_add_cancel]
        apply Finset.Ico_disjoint_Ico_consecutive
        apply Nat.one_le_pow _ _ hn
      rw [this, Finset.sum_union hh, ih, h1]
      simp

  -- sum from 1 to M is from 1 to (Nat.sqrt M)^2-1, add sum from (Nat.sqrt M)^2 to M.
  -- the former is Nat.sqrt M - 1, and latter is (M - (Nat.sqrt M)^2 + 1) times (1/(2(Nat.sqrt M)+1))
  suffices h: (Finset.Icc 1 M = (Finset.Icc 1 ((Nat.sqrt M)^2 - 1))
    ∪ (Finset.Icc ((Nat.sqrt M)^2) M)) ∧
    Disjoint (Finset.Icc 1 ((Nat.sqrt M)^2 - 1)) (Finset.Icc ((Nat.sqrt M)^2) M) by
    have: 0 < Nat.sqrt M := Nat.sqrt_pos.mpr hM
    rw [h.left, Finset.sum_union h.right, h2 this]
    simp only [Real.nat_floor_real_sqrt_eq_nat_sqrt,
    Int.cast_natCast, add_right_inj]
    replace: ∀ i ∈ Finset.Icc ((Nat.sqrt M)^2) M,
      1 / (2*(Nat.sqrt i) + 1: ℝ) = 1 / (2*(Nat.sqrt M) + 1) := by
      intro i hi
      suffices i ∈ Finset.Icc ((Nat.sqrt M)^2) ((Nat.sqrt M+1)^2-1) by
        rw [l_nat_sqrt_eq_of_mem_Icc this]
      simp only [Finset.mem_Icc] at hi ⊢
      refine ⟨hi.left, hi.right.trans ?_⟩
      suffices M+1 ≤ (M.sqrt + 1)^2 by
        exact Nat.le_sub_one_of_lt this
      exact Nat.succ_le_succ_sqrt' M
    rw [Finset.sum_congr rfl this, ← Finset.sum_div]
    rw [Real.floor_real_sqrt_eq_nat_sqrt]
    congr 2
    simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
    rw [Nat.cast_sub (by linarith only [Nat.sqrt_le' M])]
    push_cast; ring

  have hh1: Finset.Icc 1 M = Finset.Ico 1 (M+1) := rfl
  have hh2: Finset.Icc 1 (M.sqrt^2-1) = Finset.Ico 1 (M.sqrt^2-1+1) := rfl
  have hh3: Finset.Icc (M.sqrt^2) M = Finset.Ico (M.sqrt^2) (M+1) := rfl
  have: 1 ≤ M.sqrt^2 := Nat.one_le_pow _ _ (Nat.sqrt_pos.mpr hM)
  constructor
  · rw [hh1, hh2, hh3, Nat.sub_add_cancel this,
    Finset.Ico_union_Ico_eq_Ico this]
    linarith only [Nat.sqrt_le' M]
  · nth_rw 2 [← Nat.sub_add_cancel this]
    apply Finset.Ico_disjoint_Ico_consecutive