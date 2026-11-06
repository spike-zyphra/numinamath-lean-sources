import Mathlib

/- Let $a_{1}, \ldots, a_{n}$ be integers. Show that there exist $1 \leqslant \mathfrak{i}_{1}<\ldots<\mathfrak{i}_{r} \leqslant n$ such that $a_{i_{1}}+\ldots+a_{i_{r}}$ is divisible by $n$. -/

-- lemma to write Icc a c as union of Icc a b and Icc (b+1) c
lemma l_icc_union {n : ℕ} [NeZero n] (a b c : Fin n) (h : a ≤ b) (h' : b < c) :
    Finset.Icc a b ∪ Finset.Icc (b + 1) c = Finset.Icc a c := by
  ext x
  simp
  have hn : 1 < n := by omega
  constructor
  . rintro h
    obtain h | h := h
    . simp [h.left]
      trans b
      . exact h.right
      . exact h'.le
    . simp [h.right]
      trans b + 1
      . rw [Fin.le_def]
        rw [Fin.val_add_eq_of_add_lt]
        all_goals simp [Nat.mod_eq_of_lt hn]
        . omega
        . omega
      . exact h.left
  . rintro h
    obtain h' | h' := le_or_gt x b
    . left
      simp [h', h.left]
    . right
      simp [h.right]
      rw [Fin.le_def, Fin.val_add_eq_of_add_lt]
      all_goals simp [Nat.mod_eq_of_lt hn]
      . omega
      . omega

-- lemma to show  Icc a b and Icc (b+1) c are disjiont
lemma l_icc_disjoint {n : ℕ} [NeZero n] (a b c : Fin n) (h : a ≤ b) (h' : b < c) :
    Disjoint (Finset.Icc a b) (Finset.Icc (b + 1) c) := by
  rw [Finset.disjoint_left]
  rintro x hx
  simp at hx ⊢
  rintro hx'
  rw [Fin.le_def, Fin.le_def] at hx
  rw [Fin.le_def] at hx'
  have hn : 1 < n := by omega
  rw [Fin.val_add_eq_of_add_lt] at hx'
  . simp [Nat.mod_eq_of_lt hn] at hx'
    omega
  . simp [Nat.mod_eq_of_lt hn]
    omega

-- in a n length sequence we can find a consecutive subsequence divisible by n
lemma l_divisible_sum {n : ℕ} (hn : 0 < n) (a : Fin n → ℤ) :
    ∃ (i j : Fin n), i ≤ j ∧ (∑ i ∈ Finset.Icc i j, a i) % n = 0 := by
  haveI : NeZero n := ⟨by omega⟩
  let sum (i : Fin n) : ℤ := (∑ x ∈ Finset.Icc 0 i, a x) % n
  -- the prefix sums modulo n is subset of [0, n-1]
  have h_image : Finset.image sum Finset.univ ⊆ Finset.Icc 0 (n - 1) := by
    rw [Finset.subset_iff]
    rintro x hx
    simp [sum] at hx ⊢
    obtain ⟨k, hk⟩ := hx
    rw [← hk]
    and_intros
    . apply Int.emod_nonneg
      norm_cast
      omega
    . suffices (∑ x ∈ Finset.Icc 0 k, a x) % n < n by omega
      apply Int.emod_lt_of_pos
      simpa
  by_cases h_inj : Function.Injective sum
  -- if injective, then image is [0, n-1] and there is prefix sum mapping to 0
  . have h_card := Finset.card_image_of_injective Finset.univ h_inj
    simp at h_card
    replace h_image := Finset.eq_of_subset_of_card_le h_image (by simp [h_card])
    have h_zero : 0 ∈ Finset.image sum Finset.univ := by
      rw [h_image]
      simp
      omega
    simp at h_zero
    obtain ⟨a, ha⟩ := h_zero
    use 0, a, (by simp)
  -- if not injective there are two i, j where prefix sum modulo n is same, then the non-common suffix is 0 modulo n
  . rw [Function.not_injective_iff] at h_inj
    obtain ⟨i, j, h, hab⟩ := h_inj
    wlog hab' : i < j generalizing i j
    . apply this j i h.symm hab.symm (by omega)
    use i + 1, j
    and_intros
    . rw [Fin.lt_def] at hab'
      rw [Fin.le_def]
      have := Fin.is_le' (a := j)
      have : 1 % n ≤ 1 := Nat.mod_le 1 n
      rw [Fin.val_add_eq_of_add_lt]
      all_goals (simp; omega)
    . simp [sum] at h
      have : ∑ i ∈ Finset.Icc (i + 1) j, a i = (∑ i ∈ Finset.Icc 0 j, a i) - (∑ i ∈ Finset.Icc 0 i, a i) := by
        rw [← l_icc_union 0 i j (by simp) hab', Finset.sum_union (l_icc_disjoint 0 i j (by simp) hab')]
        simp
      rw [this, Int.sub_emod, h]
      simp

theorem number_theory_149904 (n : ℕ) (hn : 0 < n) (a : Fin n → ℤ) :
    ∃ r : ℕ, 0 < r ∧ ∃ i : Fin r → Fin n,
    (∀ j k, j < k → i j < i k) ∧ (∑ j, a (i j)) % n = 0 := by
    -- by lemma there is consecutive subsequence with 0 sum modulo n, using that define the function
    obtain ⟨i, j, h1, h2⟩ := l_divisible_sum hn a
    use (j - i + 1)
    and_intros
    . replace h1 := Fin.val_le_of_le h1
      omega
    . let r (k : Fin (j - i + 1)) : Fin n := by
        refine ⟨i + k, ?_⟩
        have := Fin.is_le' (a := k)
        omega
      use r
      -- rest is just mapping definitions
      and_intros
      . rintro k1 k2 hk
        simpa [r]
      . convert h2 using 2
        rw [eq_comm]
        have hr (a b : Fin (j - i + 1)) (h : r a = r b) : a = b := by
          simp [r] at h
          apply Fin.eq_of_val_eq h
        have h := Finset.sum_image (f := a) (g := r) (s := Finset.univ) (by simpa)
        convert h
        ext x
        simp
        constructor
        . rintro ⟨hx1, hx2⟩
          have := Fin.val_le_of_le h1
          have := Fin.val_le_of_le hx1
          have := Fin.val_le_of_le hx2
          use ⟨x - i, by omega⟩
          simp [r]
          apply Fin.eq_of_val_eq
          simp
          omega
        . rintro ⟨a, ha⟩
          simp [r] at ha
          rw [← ha, Fin.le_def, Fin.le_def]
          simp
          omega