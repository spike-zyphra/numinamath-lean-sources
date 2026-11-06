import Mathlib

def isJuicy (j : ℕ) : Prop :=
  j > 1 ∧ ∃ (a : Finset ℕ) (hs : a.Nonempty),
    (∀ x ∈ a, 0 < x) ∧
    a.max' hs = j ∧
    ∑ x ∈ a, (1 : ℚ) / x = 1

/-Show that if j is a juicy integer, then 2j is juicy as well.
Remark: A juicy number is an integer j > 1 for which there is a sequence a1 < a2 < ... < ak of positive
integers such that ak = j and such that the sum of the reciprocals of all the ai
is 1.-/
theorem number_theory_608462(j : ℕ) (h : isJuicy j) : isJuicy (2 * j) := by

  -- Unpack the hypothesis that j is juicy --
  simp [isJuicy] at h
  rcases h with ⟨j_ge_one,a,a_pos,a_max,a_sum⟩

  -- Construct the new set by doubling each element and adding 2 --
  let a' : Finset ℕ := insert 2 (a.map ⟨(· * 2), fun x y ↦ by simp⟩)

  -- Prove that a' is nonempty (since 2 is inserted) --
  have hs' : a'.Nonempty := Finset.insert_nonempty 2 _

  -- Prove that all elements of a' are positive
  have a'_pos : ∀ x ∈ a', 0 < x := by
    intro x hx
    apply Finset.mem_insert.mp at hx
    rcases hx with hx | hx
    . omega
    . simp at hx
      obtain ⟨a1,ha1⟩ := hx
      rcases ha1 with ⟨ha1,ha2⟩
      specialize a_pos a1 ha1
      omega

  -- Prove that the largest element is 2j --
  have a'_max : a'.max' hs' = 2 * j:= by
    refine le_antisymm ?_ ?_
    · apply Finset.max'_le
      intro x hx
      simp [a'] at hx
      rcases hx with hx | hx
      . omega
      . obtain ⟨a1,ha1⟩ := hx
        rcases ha1 with ⟨ha1,ha2⟩
        obtain ⟨hs, a_max⟩ := a_max
        have ba1: a1 ≤ a.max' hs := by
          apply Finset.le_max' a a1 ha1
        rw [a_max] at ba1
        omega
    . obtain ⟨hs,a_max⟩ := a_max
      have hj: j ∈ a := by
        rw [← a_max]
        apply Finset.max'_mem a hs
      have hj': 2 * j ∈ a' := by
        simp [a']
        right
        use j
        simp [hj]
        omega
      apply Finset.le_max'
      exact hj'

  -- Prove that the sum of reciprocals is 1
  have a'_sum : ∑ x ∈ a', (1 : ℚ) / x = 1 := by
    rw [Finset.sum_insert]
    simp [Finset.sum_map]
    have sum_eq: 2⁻¹ * (∑ x ∈ a, (x: ℚ)⁻¹) = ∑ x ∈ a, 2⁻¹ * (x: ℚ)⁻¹ := by
      apply Finset.mul_sum
    rw [← sum_eq]
    simp [a_sum]
    norm_num
    simp
    by_contra! o
    have a_card: a.card ≤ 1 := by
      by_contra! a_card
      rw [Finset.one_lt_card] at a_card
      obtain ⟨p,hp,q,hq,hpq⟩ := a_card
      by_cases pa: p ≠ 1
      -- Case 1: p ≠ 1 --
      . have no:  ∑ x ∈ a, (↑x)⁻¹ ≥ 1 + (p: ℚ)⁻¹ := by
          have hp_a: p ∈ a.erase 1 := by
            apply Finset.mem_erase.mpr
            constructor
            . intro h
              rw [h] at hp
              omega
            . exact hp
          have eq1:  (1: ℚ)⁻¹ + (∑ x ∈ a.erase 1, (x: ℚ)⁻¹) = ∑ x ∈ a, (x: ℚ)⁻¹:= by
            apply Finset.add_sum_erase a (fun x ↦ (x : ℚ)⁻¹) o
          have eq2: (p: ℚ)⁻¹ + ∑ x ∈ (a.erase 1).erase p, (x: ℚ)⁻¹ = ∑ x ∈ a.erase 1, (x: ℚ)⁻¹ := by
            apply Finset.add_sum_erase (a.erase 1) (fun x ↦ (x : ℚ)⁻¹) hp_a
          have eq3: ∑ x ∈ a, (↑x)⁻¹ = (1: ℚ)⁻¹ + (p: ℚ)⁻¹ + ∑ x ∈ (a.erase 1).erase p, (x: ℚ)⁻¹ := by
            rw [← eq1]
            rw [← eq2]
            ring
          have ineq: 0 ≤ ∑ x ∈ (a.erase 1).erase p, (x: ℚ)⁻¹ := by
            apply Finset.sum_nonneg
            simp
          simp [ineq,eq3]
        rw [a_sum] at no
        absurd no
        simp
        specialize a_pos p hp
        omega
      . -- case 2: p = 1, so q ≠ 1--
        simp at pa
        have qa: q ≠ 1 := by omega
        -- similar to the previous case --
        have no:  ∑ x ∈ a, (↑x)⁻¹ ≥ 1 + (q: ℚ)⁻¹ := by
          have hq_a: q ∈ a.erase 1 := by
            apply Finset.mem_erase.mpr
            constructor
            . intro h
              rw [h] at hq
              omega
            . exact hq
          have eq1:  (1: ℚ)⁻¹ + (∑ x ∈ a.erase 1, (x: ℚ)⁻¹) = ∑ x ∈ a, (x: ℚ)⁻¹:= by
            apply Finset.add_sum_erase a (fun x ↦ (x : ℚ)⁻¹) o
          have eq2: (q: ℚ)⁻¹ + ∑ x ∈ (a.erase 1).erase q, (x: ℚ)⁻¹ = ∑ x ∈ a.erase 1, (x: ℚ)⁻¹ := by
            apply Finset.add_sum_erase (a.erase 1) (fun x ↦ (x : ℚ)⁻¹) hq_a
          have eq3: ∑ x ∈ a, (↑x)⁻¹ = (1: ℚ)⁻¹ + (q: ℚ)⁻¹ + ∑ x ∈ (a.erase 1).erase q, (x: ℚ)⁻¹ := by
            rw [← eq1]
            rw [← eq2]
            ring
          have ineq: 0 ≤ ∑ x ∈ (a.erase 1).erase q, (x: ℚ)⁻¹ := by
            apply Finset.sum_nonneg
            simp
          simp [ineq,eq3]
        rw [a_sum] at no
        absurd no
        simp
        specialize a_pos q hq
        omega
    -- Now we will show that we must have a = {1} --
    rcases a_max with ⟨a_nonempty, amax⟩
    replace a_card: a.card = 1 := by
      by_contra! a_card
      replace a_card: a.card = 0 := by
        omega
      simp at a_card
      rw [a_card] at a_nonempty
      tauto
    have a_card2:= a_card
    rw [Finset.card_eq_one] at a_card
    obtain ⟨a1, ha1⟩ := a_card
    have a1_eq: a1 = 1 := by
      by_contra! a1_eq
      have no: 1 < a.card := by
        rw [Finset.one_lt_card_iff]
        use a1
        use 1
        constructor
        . simp [ha1]
        . constructor
          . simp [o]
          . simp [a1_eq]
      rw [a_card2] at no
      tauto
    rw [a1_eq] at ha1
    -- the final step --
    have am: a.max' a_nonempty = 1 := by
      simp [ha1]
    rw [am] at amax
    omega

  -- Combine all results to prove that 2j is juicy --
  simp [isJuicy]
  constructor
  . omega
  . use a'
    constructor
    . exact a'_pos
    . constructor
      . simp [a'_max]
        exact hs'
      . simp at a'_sum
        exact a'_sum