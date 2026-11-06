import Mathlib

/- Let $z_{0} < z_{1} < z_{2} < \cdots$ be an infinite sequence of positive integers. Prove that there exists a unique integer $n \geqslant 1$ such that  $$ z_{n}<\frac{z_{0}+z_{1}+\cdots+z_{n}}{n} \leqslant z_{n+1} $$  (Austria) -/
theorem number_theory_24386 (z : ℕ → ℤ) (hz : ∀ n, z n > 0)
    (hzn : ∀ n, z n < z (n + 1)) :
    ∃! n ≥ 1, z n < (∑ i in Finset.Icc 0 n, z i) / (n : ℝ) ∧ (∑ i in Finset.Icc 0 n, z i) / (n : ℝ) ≤ z (n + 1) := by

    -- we start by proving the following lemma:
    -- given a sequence a_0 > a_1 > ... of integers, where a_0 > 0,
    -- there is a unique index n such that a_n > 0 ≥ a_{n+1}

    -- first we prove the existence of this index n
    have desc_seq_zero (a : ℕ → ℤ) (ha : ∀ n, a n > a (n + 1)) (ha₀ : a 0 > 0) :
      ∃ n, a n > 0 ∧ a (n + 1) ≤ 0 := by

      -- the following bound is obtained by induction, from the fact that
      -- each a_{n+1} is at most a_{n} - 1.
      have hsub : ∀ n, a n ≤ a 0 - n := by
        intro n
        induction n
        case zero => simp
        case succ n ih =>
          have : a (n + 1) ≤ a n - 1 := by exact Int.le_sub_one_of_lt (ha n)
          have : a 0 - ↑(n + 1) = a 0 - n - 1 := by
              rw [Nat.cast_add_one]
              ring
          rw [this]
          linarith

      -- now we prove the existence of n by contradiction
      by_contra! h
      -- as a consequence, we have that all values in a_n are positive
      have hpos : ∀ n, a n > 0 := by
        intro n
        induction n
        case zero => exact ha₀
        case succ n ih => exact h n ih
      -- we can build contradiction from the following facts:
      -- 1. a_{a_0} ≤ a_0 - a_0 = 0
      have h₁ := hsub ((a 0).toNat)
      have h₂ : a 0 - ↑((a 0).toNat) ≤ 0 := by simp
      -- 2. a_{a_0} > 0
      have h₃ := hpos ((a 0).toNat)
      -- so we use linarith to find the contradiction
      linarith

    -- the next lemma strengthen the previous one by asserting uniqueness of n
    have desc_seq_unique_zero (a : ℕ → ℤ) (ha : ∀ n, a n > a (n + 1)) (ha₀ : a 0 > 0) :
      ∃! n, a n > 0 ∧ a (n + 1) ≤ 0 := by
      -- we first derive that a_n is antitone
      have anti_a : Antitone a := by apply antitone_of_succ_le; exact fun a_1 _ ↦ Int.le_of_lt (ha a_1)
      -- the existence of such an index n is obtained by the previous lemma, we directly use it
      have ⟨n, ⟨han, han'⟩⟩ := desc_seq_zero a ha ha₀
      use n, ⟨han, han'⟩

      -- next we prove n is unique, that is, if m also satisfies a_m > 0 ≥ a_{m+1}, then m = n
      rintro m ⟨ham, ham'⟩
      -- we must have m ≤ n, otherwise a_m ≤ a_{n + 1} ≤ 0
      have : m ≤ n := by
        by_contra! h
        have := Antitone.imp anti_a h
        linarith
      -- we must have m ≥ n, otherwise a_{m+1} ≥ a_n > 0
      have : m ≥ n := by
        by_contra! h
        have := Antitone.imp anti_a h
        linarith
      -- so it must be m = n, and we find this by linarith
      linarith

    -- Now we prove the theorem. We define the sequence d_n by
    -- d_n := z_0 + ... + z_n - n * z_n
    -- d is strictly decreasing from d_1, so we need an auxiliary sequence d'_n = d_{n+1}
    let d : ℕ → ℤ := fun n ↦ (∑ i in Finset.Icc 0 n, z i) - n * z n
    let d' : ℕ → ℤ := fun n ↦ d (n + 1)

    -- the conditions in the theorem can be equivalently expressed in terms of d
    -- 1. z_n < (z_0 + ... + z_n) / n ↔ d_n > 0
    have h_equiv_d_1 (n : ℕ) (hn : n ≥ 1) : z n < (∑ i in Finset.Icc 0 n, z i) / (n : ℝ) ↔ d n > 0 := by
      unfold d
      field_simp
      constructor
      · intro h
        rw [lt_div_iff₀' (Nat.cast_pos'.mpr hn)] at h
        norm_cast at h
      · intro h
        rw [lt_div_iff₀' (Nat.cast_pos'.mpr hn)]
        norm_cast

    -- 2. (z_0 + ... + z_n) / n ≤ z_{n+1} ↔ d_{n+1} ≤ 0
    have h_equiv_d_2 (n : ℕ) (hn : n ≥ 1) : (∑ i in Finset.Icc 0 n, z i) / (n : ℝ) ≤ z (n + 1) ↔ d (n + 1) ≤ 0 := by
      unfold d
      rw [div_le_iff₀', ← sub_nonpos, Finset.sum_Icc_succ_top, Nat.cast_add_one]
      norm_cast
      have : z (n + 1) - ↑(n + 1) * z (n + 1) = - n * z (n + 1) := by
        rw [Nat.cast_add_one]
        ring
      rw [add_sub_assoc, this]
      simp
      exact Nat.le_add_left 0 (n + 1)
      exact Nat.cast_pos'.mpr hn

    -- by unfolding definitions, the sequence d' satisfy d'_0 > 0 and d'_n > d'_{n+1}
    have hd₀ : d' 0 > 0 := by
      unfold d' d
      simp
      nth_rw 2 [(by rfl : 1 = 0 + 1)]
      rw [Finset.sum_Icc_succ_top]
      simp [hz 0]
      norm_num
    have hdn : ∀ n, d' n > d' (n + 1) := by
      unfold d' d
      intro n
      apply lt_of_sub_neg
      rw [Finset.sum_Icc_succ_top (by simp), (by ring : n + 1 + 1 = n + 2)]
      simp_all
      have : (↑n + 2) * z (n + 2) = z (n + 2) + (n + 1) * z (n + 2) := by ring
      rw [this]
      suffices h : (n + 1) * z (n + 1) - (n + 1) * z (n + 2) < 0 by linarith
      simp
      exact hzn (n + 1)

    -- so we have unique index n such that d'_n > 0 ≥ d'_{n+1}
    have ⟨n, ⟨⟨hn₁, hn₂⟩, h_uniq⟩⟩ := desc_seq_unique_zero d' hdn hd₀
    -- and this is equivalent to d_{n+1} > 0 ≥ d_{n+2}
    unfold d' at hn₁ hn₂  h_uniq
    rw [(by simp : n + 1 + 1 = n + 2)] at hn₂

    -- so we use n+1 as the desired index
    use (n + 1)
    simp

    constructor
    · -- we need to prove that n+1 meets the desired conditions
      have p1 := (h_equiv_d_1 (n + 1) (by simp)).mpr hn₁
      have p2 := (h_equiv_d_2 (n + 1) (by simp)).mpr hn₂
      norm_cast at *
    · -- and also show that n+1 is unique
      rintro n' n'ge hn'₁ hn'₂
      rw [← Int.cast_sum] at hn'₁ hn'₂
      have p1' := (h_equiv_d_1 (n') n'ge).mp hn'₁
      have p2' := (h_equiv_d_2 (n') n'ge).mp hn'₂
      have : ∃ n'', n' = n'' + 1 := by exact Nat.exists_eq_add_one.mpr n'ge
      have ⟨n'', heq⟩ := this
      rw [heq]
      rw [heq] at p1' p2'
      have := h_uniq (n'') ⟨p1', p2'⟩
      linarith
