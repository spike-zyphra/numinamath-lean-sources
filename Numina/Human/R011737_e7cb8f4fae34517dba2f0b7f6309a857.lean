import Mathlib

/-7 Let $m, n$ be integers, $m>n \geqslant 2, S=\{1,2, \cdots, m\}, T=$ $\left\{a_{1}, a_{2}, \cdots, a_{n}\right\}$ be a subset of $S$. It is known that any two numbers in $T$ cannot simultaneously divide any number in $S$. Prove:
$\frac{1}{a_{1}}+\frac{1}{a_{2}}+\cdots+\frac{1}{a_{n}}<\frac{m+n}{m}$.
(Supplied by Zhang Tongjun)-/
theorem inequalities_285538 (m n : ℕ) (hn : 2 ≤ n) (hm : n < m)
  (T : Finset ℕ) (hT : T ⊆ Finset.Icc 1 m) (hT1 : T.card = n)
  (hT2 : ∀ x ∈ T, ∀ y ∈ T, ∀ z ∈ Finset.Icc 1 m, x ≠ y → ¬(x ∣ z ∧ y ∣ z)) :
  ∑ x ∈ T, (1 : ℚ)/x < (m + n)/m := by

  let S := Finset.Icc 1 m
  let T_type := {a : ℕ // a ∈ T}

  -- 构造 $ T_i={ b \in S : a_i | b }, i=1,2, \cdots, n $.
  let T' (a_i : T_type) : Finset ℕ := {b ∈ S | a_i.val ∣ b}

  --  则 $ |T_i|=[ \frac{m}{a_i} ] $
  have h_T'_card {a : ℕ} (amem : a ∈ T) : (T' ⟨a, amem⟩).card = m / a := by
    unfold T' S
    simp
    rw [show Finset.Icc 1 m = Finset.Ioc 0 m by rfl]
    exact Nat.Ioc_filter_dvd_card_eq_div m a

  -- 由于 $T$ 中任意两个数都不能同时整除 $S$ 中的一个数, 所以当 $i \neq j$时, $T_i \cap T_j=\varnothing$.
  have h_T'_disjoint {a₁ a₂ : ℕ} (h₁ : a₁ ∈ T) (h₂ : a₂ ∈ T) : a₁ ≠ a₂ →
    Disjoint (T' ⟨a₁, h₁⟩) (T' ⟨a₂, h₂⟩) := by
      intro h_ne
      refine Finset.disjoint_filter.mpr ?_
      intro z zmem
      simp
      intro ha₁_dvd ha₂_dvd
      apply hT2 a₁ h₁ a₂ h₂ z zmem h_ne ⟨ha₁_dvd, ha₂_dvd⟩

  have h_T'_pairwise_disjoint : ((.univ : Finset T_type) : Set T_type).PairwiseDisjoint T' := by
    intro a₁ a₁mem a₂ a₂mem  h_ne
    apply h_T'_disjoint
    exact Subtype.coe_ne_coe.mpr h_ne

  have h_biUnion_T'_card_eq := Finset.card_biUnion h_T'_pairwise_disjoint

  have h_sum_T'_card_eq : ∑ a : T_type, (T' a).card = ∑ a ∈ T, m / a := by
    let i : T_type → ℕ := fun ⟨a, amem⟩ ↦ a
    apply Finset.sum_nbij (i := i)
    · simp [i]
    · intro a₁ a₁mem a₂ a₂mem h_eq
      unfold i at h_eq
      simp at h_eq
      exact Subtype.eq h_eq
    · intro x xmem
      simp
      use ⟨x, xmem⟩
    · intro a amem
      exact h_T'_card a.property

  -- 则 $$ \sum_{i=1}^{n}\left|T_{i}\right|=\sum_{i=1}^{n}\left[\frac{m}{a_{i}}\right] \leqslant m $$
  have h_biUnion_T'_card_le : (Finset.univ.biUnion T').card ≤ m := by
    have : (Finset.univ.biUnion T') ⊆ S := by
      intro s smem
      simp at smem
      have ⟨a, ha⟩ := smem
      simp [T'] at ha
      exact ha.1
    trans S.card
    · exact Finset.card_le_card this
    unfold S
    simp only [Nat.card_Icc, add_tsub_cancel_right, le_refl]

  have h_sum_m_div_a_le : ∑ a ∈ T, m / a ≤ m := by linarith

  -- 又因为 $$ \frac{m}{a_{i}} < \left[\frac{m}{a_{i}}\right]+1, $$
  have h_lt_floor_succ : ∀ a ∈ T, (m : ℚ) / a < (m / a : ℕ) + 1 := by
    intro a amem
    have : ((m / a : ℕ) : ℚ) = ⌊(m : ℚ) / a⌋ := by
      norm_cast
    rw [this]
    simp only [Int.lt_floor_add_one]

  -- 所以 $$ \begin{aligned} \sum_{i=1}^{n} \frac{m}{a_{i}} & < \sum_{i=1}^{n}\left(\left[\frac{m}{a_{i}}\right]+1\right)=\sum_{i=1}^{n}\left[\frac{m}{a_{i}}\right]+\sum_{i=1}^{n} 1 \ & \leqslant m+n \end{aligned} $$
  have h_sum_frac_lt : ∑ a ∈ T, (m : ℚ) / a < m + n := by
    have : ∑ a ∈ T, (m : ℚ) / a < ∑ a ∈ T, ((m / a : ℕ) + 1) := by
      simp only [Nat.cast_sum]
      apply Finset.sum_lt_sum_of_nonempty
      · refine Finset.card_ne_zero.mp ?_
        rw [hT1]
        linarith
      intro a amem
      rw [Nat.cast_add, Nat.cast_one]
      exact h_lt_floor_succ a amem
    rw [Nat.cast_sum] at this

    suffices h : ∑ a ∈ T, (((m / a + 1 : ℕ)) : ℚ) ≤ m + n by
      linarith

    norm_cast
    rw [Finset.sum_add_distrib]
    simp [hT1, h_sum_m_div_a_le]

  -- 即 $$ m \sum \frac{1}{a_{i}}=\sum_{i=1}^{n} \frac{m}{a_{i}} < m+n $$
  have : ∑ a ∈ T, (m : ℚ) / a = m * ∑ a ∈ T, (1 : ℚ) / a := by
    rw [Finset.mul_sum]
    congr
    ext a
    field_simp

  have h_m_mul_sum_lt : m * ∑ a ∈ T, (1 : ℚ) / a < m + n := by
    rw [this] at h_sum_frac_lt
    exact h_sum_frac_lt

  -- 所以 $$ \sum_{i=1}^{n} \frac{1}{a_{i}} < \frac{m+n}{m} $$
  apply lt_div_iff₀' ?_ |>.mpr
  · exact h_m_mul_sum_lt
  · norm_cast
    linarith
