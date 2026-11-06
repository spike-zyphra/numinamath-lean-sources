import Mathlib

/- A set $S$ is called neighbouring if it has the following two properties:
a) $S$ has exactly four elements

b) for every element $x$ of $S$, at least one of the numbers $x-1$ or $x+1$ belongs to $S$.
-/


def isNeighboring (S : Finset ℤ) : Prop :=
  S.card = 4 ∧ ∀ x ∈ S, x - 1 ∈ S ∨ x + 1 ∈ S

-- First observe that a set is neighboring if and only if there are numbers a and b separated by at least 3 and such that S = {a, a + 1, b - 1, b}.
lemma isNeighboring_iff (s : Finset ℤ) : isNeighboring s ↔ ∃ a : ℤ, ∃ b : ℤ, a + 3 ≤ b ∧ s = {a, a + 1, b - 1, b}  := by
  -- A useful sublemma
  have hl {a b : ℤ} : a + 3 ≤ b → ({a, a + 1, b - 1, b} : Finset _).card = 4 := by
    intro _
    convert Finset.card_insert_of_not_mem ?_
    simp
    convert Finset.card_insert_of_not_mem ?_
    simp
    by_contra!
    simp at this
    rcases this
    repeat linarith
    simp
    constructor
    repeat linarith

  -- Iff statement, we show both implications
  constructor

  -- First a neighboring set must be of the form {a, a + 1, b - 1, b}.
  · intro hs
    have hs₀ : s.Nonempty := by
      apply Finset.card_ne_zero.mp
      rw [hs.1]
      trivial
    let a := s.min' hs₀
    let b := s.max' hs₀
    use a
    use b
    have ha₀ : a ∈ s := by apply Finset.min'_mem
    have hb₀ : b ∈ s := by apply Finset.max'_mem
    have ha₁ : a + 1 ∈ s := by
      obtain (h|h) := hs.2 a ha₀
      · exfalso
        obtain : a ≤ a - 1 := by 
          apply Finset.min'_le
          exact h
        linarith
      · exact h
    have hb₁ : b - 1 ∈ s := by
      obtain (h|h) := hs.2 b hb₀
      · exact h
      · exfalso
        obtain : b + 1 ≤ b := by
          apply Finset.le_max'
          exact h
        linarith
    have hab : a + 3 ≤ b := by
      by_contra! h
      have hss : s ⊆ Finset.Icc a b := by
        intro x hx
        simp
        constructor
        exact Finset.min'_le _ _ hx
        exact Finset.le_max' _ _ hx
      absurd hs.1
      suffices s.card ≤ 3 by linarith
      replace hss := Finset.card_mono hss
      simp at hss
      suffices (b + 1 - a).toNat ≤ 3 by linarith
      omega

    constructor
    · exact hab
    · apply Eq.symm
      apply Finset.eq_of_subset_of_card_le
      · apply Finset.insert_subset
        assumption
        apply Finset.insert_subset
        assumption
        apply Finset.insert_subset
        assumption
        apply Finset.singleton_subset_iff.mpr
        assumption
      · rw [hs.1]
        apply le_of_eq
        apply Eq.symm
        exact hl hab

  -- Conversely such set is neighoring
  · intro h
    obtain ⟨a, b, hab, hss⟩ := h
    constructor
    · simp [hss]
      exact hl hab
    · intro x hx
      simp [hss] at hx
      rcases hx with (hx|hx|hx|hx)
      · right
        simp [hx, hss]
      · left
        simp [hx, hss]
      · right
        simp [hx, hss]
      · left
        simp [hx, hss]

/-
Find the number of all neighbouring subsets of the set $\{1,2, \ldots, n\}$.
-/
theorem combinatorics_604992 (n : ℕ) :
  (n < 3 → Set.encard {s : Finset ℤ | s ⊆ Finset.Icc 1 n ∧ isNeighboring s} = 0 ) ∧
  (n ≥ 3 → Set.encard {s : Finset ℤ | s ⊆ Finset.Icc 1 n ∧ isNeighboring s} = ((((n - 3) * (n - 2)) / (2 : ℕ)) :ENat))
  := by

  set N := { s : Finset ℤ | s ⊆ Finset.Icc 1 n ∧ isNeighboring s }
  let M := { (a, b) : ℤ × ℤ | 1 ≤ a ∧ a + 3 ≤ b ∧ b ≤ n }

  -- Using the lemma isNeighboring_iff, show that M and N are bijective so that they have the same cardinality
  have : M.encard = N.encard := by
    apply Set.encard_congr
    let f := fun (a,b) => ({a, a + 1, b - 1, b} : Finset ℤ)
    apply Set.BijOn.equiv f
    constructor
    · intro (a,b)
      rintro ⟨h₁,h₂,h₃⟩
      simp [N]
      constructor
      · apply Finset.insert_subset
        · simp [h₁]
          linarith
        apply Finset.insert_subset
        · simp
          constructor
          linarith
          linarith
        apply Finset.insert_subset
        · simp
          constructor
          repeat omega
        · simp
          constructor
          repeat linarith
      · simp [isNeighboring_iff]
        use a
        use b
    constructor
    · have hf₀: ∀ p ∈ M, (f p).Nonempty := by
        intro p hp
        use p.1
        simp [f]
      have hf₁ (p : ℤ × ℤ) (hp: p ∈ M) : (f p).min' (hf₀ p hp) = p.1 := by
        simp [f]
        apply Int.le_antisymm
        · apply Finset.min'_le
          apply Finset.mem_insert_self
        · apply Finset.le_min'
          simp
          have := hp.2.1
          constructor
          repeat omega
      have hf₂ (p : ℤ × ℤ) (hp: p ∈ M) : (f p).max' (hf₀ p hp) = p.2 := by
        simp [f]
        apply Int.le_antisymm
        · apply Finset.max'_le
          simp
          have := hp.2.1
          constructor
          repeat omega
        · apply Finset.le_max'
          simp
      intro p hp p' hp'
      intro h
      ext
      · rw [← hf₁ p hp, ← hf₁ p' hp']
        congr
      · rw [← hf₂ p hp, ← hf₂ p' hp']
        congr
    · intro S
      rintro ⟨hn,hN⟩
      obtain ⟨a, b, hab⟩ := (isNeighboring_iff S).mp hN
      use (a,b)
      constructor
      · constructor
        · have ha : a ∈ S := by
            simp [hab.2]
          replace ha := hn ha
          simp at ha
          exact ha.1
        constructor
        · exact hab.1
        · have hb : b ∈ S := by
            simp [hab.2]
          replace hb := hn hb
          simp at hb
          exact hb.2
      · simp [f, hab.2]

  -- Now we can forget about the set N
  rw [← this]

  -- We count the number of elements of M
  -- The case n = 0, 1, 2 is immediate
  constructor
  · intro hn
    simp [M]
    apply Set.eq_empty_of_forall_not_mem
    intro (a,b)
    by_contra h
    simp at h
    omega

  -- Assume now n ≥ 3
  intro _
  -- Write m = n - 2 so that the anwser is m choose 2
  set m := n - 2
  rw [(by omega : n - 3 = m - 1)]
  rw [mul_comm, ← Nat.choose_two_right]

  -- It suffices to show that M is in bijective with the set of pairs in {1, ..., m}
  suffices M ≃ (((Finset.Icc 1 (m : ℤ)).powersetCard 2): Set (Finset ℤ)) by
    have hc : M.encard = (((Finset.Icc 1 (m : ℤ)).powersetCard 2) : Set (Finset ℤ)).encard := by
      apply Set.encard_congr
      simpa
    rw [hc]
    simp

  -- The bijection is given by (a,b) ↦ {a, b - 2}
  let f := fun (a,b) => ({a, b - 2} : Finset ℤ)
  apply Set.BijOn.equiv f
  constructor
  · intro p hp
    simp [f]
    simp [M] at hp
    constructor
    · intro x hx
      simp at hx
      cases hx
      · simp
        constructor
        linarith
        omega
      · simp
        constructor
        repeat omega
    · apply Finset.card_pair
      omega
  constructor
  · have hf₀: ∀ p ∈ M, (f p).Nonempty := by
      intro p hp
      use p.1
      simp [f]
    have hf₁ (p : ℤ × ℤ) (hp: p ∈ M) : (f p).min' (hf₀ p hp) = p.1 := by
      simp [f]
      apply Int.le_antisymm
      · apply Finset.min'_le
        apply Finset.mem_insert_self
      · apply Finset.le_min'
        simp
        have := hp.2.1
        omega
    have hf₂ (p : ℤ × ℤ) (hp: p ∈ M) : (f p).max' (hf₀ p hp) = p.2 - 2 := by
      simp [f]
      apply Int.le_antisymm
      · apply Finset.max'_le
        simp
        have := hp.2.1
        omega
      · apply Finset.le_max'
        simp
    intro p hp p' hp'
    intro h
    ext
    · rw [← hf₁ p hp, ← hf₁ p' hp']
      congr
    · suffices p.2 - 2 = p'.2 - 2 by
        linarith
      rw [← hf₂ p hp, ← hf₂ p' hp']
      congr

  -- The map is surjective
  · intro s hs
    simp at hs
    have hs₀ : s.Nonempty := by
      apply Finset.card_ne_zero.mp
      rw [hs.2]
      linarith
    have hsm : s.min' hs₀ < s.max' hs₀ := by
      apply Finset.min'_lt_max'_of_card
      rw [hs.2]
      trivial
    use (s.min' hs₀, s.max' hs₀ + 2)
    constructor
    · constructor
      · suffices s.min' hs₀ ∈ Finset.Icc 1 (m : ℤ) by
          simp only [Finset.mem_Icc] at this
          exact this.1
        apply hs.1
        apply Finset.min'_mem
      constructor
      · omega
      · suffices s.max' hs₀ ∈ Finset.Icc 1 (m : ℤ) by
          simp only [Finset.mem_Icc] at this
          omega
        apply hs.1
        apply Finset.max'_mem
    · simp [f]
      ext x
      simp
      constructor
      · rintro (hx|hx) <;>
        rw [hx]
        apply Finset.min'_mem
        apply Finset.max'_mem
      · intro hx
        by_contra! h
        obtain ⟨h₁,h₂⟩ := h
        absurd hs.2
        suffices s.card ≥ 3 by linarith
        apply Finset.le_card_iff_exists_subset_card.mpr
        use {x, s.min' hs₀, s.max' hs₀}
        constructor
        · apply Finset.insert_subset
          assumption
          apply Finset.insert_subset
          apply Finset.min'_mem
          apply Finset.singleton_subset_iff.mpr
          apply Finset.max'_mem
        · suffices ({s.min' hs₀, s.max' hs₀} : Finset ℤ).card = 2 by
            rw [(by trivial : 3 = 2 + 1), ← this]
            apply Finset.card_insert_of_not_mem
            simp
            constructor
            repeat assumption
          rw [Finset.card_eq_two]
          use s.min' hs₀
          use s.max' hs₀
          constructor
          · apply ne_of_lt
            exact hsm
          · rfl