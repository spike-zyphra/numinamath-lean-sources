import Mathlib

set_option maxHeartbeats 400000

/- Let $A$ and $B$ be sets of positive integers with $|A| \geq 2$ and $|B| \geq 2$. Let $S$ be a set consisting of $|A|+|B|-1$ numbers of the form $a b$ where $a \in A$ and $b \in B$. Prove that there exist pairwise distinct $x, y, z \in S$ such that $x$ is a divisor of $y z$. -/
theorem number_theory_604484 (A B S : Finset ℕ)
    (hA : ∀ a ∈ A, a > 0) (hB : ∀ b ∈ B, b > 0)
    (h₀ : A.card ≥ 2) (h₁ : B.card ≥ 2)
    (h₂ : S.card = A.card + B.card - 1)
    (h₃ : ∀ x ∈ S, ∃ a ∈ A, ∃ b ∈ B, x = a * b) :
    ∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S, x ≠ y ∧ y ≠ z ∧ z ≠ x ∧ x ∣ y * z := by

    -- let k := |S|, We use induction on $k=|A|+|B|-1$.
    generalize hk_eq : S.card = k

    have hk: k ≥ 3 := by
      rw [← hk_eq, h₂, show 3 = 2 + 2 - 1 by norm_num]
      gcongr

    induction k, hk using Nat.le_induction generalizing S A B
    case base =>
      -- For $k=3$ we have $|A|=|B|=2$.
      have : A.card = 2 := by
        rw [h₂] at hk_eq
        by_contra! h
        have : A.card ≥ 3 := by exact Nat.lt_of_le_of_ne h₀ (id (Ne.symm h))
        have : A.card + B.card - 1 ≥ 4 := by
          rw [show 4 = 3 + 2 - 1 by norm_num]
          gcongr
        linarith

      -- Let A = {x, y}.
      have ⟨x, y, hxy, hA_eq⟩ := Finset.card_eq_two.mp this
      rw [hA_eq] at hA; simp at hA
      have xnz : x ≠ 0 := Nat.ne_zero_iff_zero_lt.mpr hA.1
      have ynz : y ≠ 0 := Nat.ne_zero_iff_zero_lt.mpr hA.2

      have : B.card = 2 := by
        rw [h₂] at hk_eq
        by_contra! h
        have : B.card ≥ 3 := by exact Nat.lt_of_le_of_ne h₁ (id (Ne.symm h))
        have : A.card + B.card - 1 ≥ 4 := by
          rw [show 4 = 2 + 3 - 1 by norm_num]
          gcongr
        linarith

      -- and let B = {s, t}
      have ⟨s, t, hst, hB_eq⟩ := Finset.card_eq_two.mp this
      rw [hB_eq] at hB; simp at hB
      have snz : s ≠ 0 := Nat.ne_zero_iff_zero_lt.mpr hB.1
      have tnz : t ≠ 0 := Nat.ne_zero_iff_zero_lt.mpr hB.2

      -- Then $S$ consists of three numbers from the set {x * z, y * z, x * t, y * t}.
      have h_S_subset : S ⊆ {x * s, x * t, y * s, y * t} := by
        intro z zmem
        have ⟨a, amem, b, bmem, hz_eq⟩ := h₃ z zmem
        rw [hz_eq]
        simp [hA_eq] at amem
        simp [hB_eq] at bmem
        rcases amem with ha | ha
        all_goals rcases bmem with hb | hb
        all_goals rw [ha, hb]
        all_goals simp

      -- one element in {x * z, y * z, x * t, y * t} may be missing in S
      -- case 1 : x * s ∉ S, we have y * t ∣ x * t * y * s
      by_cases hxs : x * s ∉ S
      · have h_S_subset' : S ⊆ {x * s, x * t, y * s, y * t} \ {x * s} := by
          refine Finset.subset_sdiff.mpr ?_
          constructor
          · exact h_S_subset
          exact Finset.disjoint_singleton_right.mpr hxs

        by_cases h' : x * s = y * t
        · have : {x * s, x * t, y * s, y * t} \ {x * s} = ({x * t, y * s} : Finset ℕ) := by
            ext z
            constructor
            · intro hz
              simp at hz
              rcases hz.1 with rfl | rfl | rfl |rfl
              all_goals simp [h'] at hz ⊢
            · intro hz
              simp at hz
              rcases hz with rfl | rfl
              · simp; use hst.symm
              · simp; use hxy.symm
          rw [this] at h_S_subset'
          have : ({x * t, y * s} : Finset ℕ).card ≤ 2 := by exact Finset.card_le_two
          have : S.card ≤ 2 := by
            trans ({x * t, y * s} : Finset ℕ).card
            exact Finset.card_le_card h_S_subset'
            exact this
          linarith

        have : {x * s, x * t, y * s, y * t} \ {x * s} = ({x * t, y * s, y * t} : Finset ℕ) := by
          ext z
          constructor
          · intro hz
            simp at hz
            rcases hz.1 with rfl | rfl | rfl |rfl
            all_goals simp [h'] at hz ⊢
          · intro hz
            simp at hz
            rcases hz with rfl | rfl | rfl
            all_goals simp  [hst.symm, hxy.symm]
            · refine Nat.ne_zero_iff_zero_lt.mpr hA.1
            · refine Nat.ne_zero_iff_zero_lt.mpr hB.1
            · exact fun x ↦ h' x.symm
        rw [this] at h_S_subset'

        have : S = ({x * t, y * s, y * t} : Finset ℕ) := by
          apply Finset.eq_of_subset_of_card_le
          exact h_S_subset'
          trans 3
          exact Finset.card_le_three
          exact Nat.le_of_eq (id (Eq.symm hk_eq))
        rw [this]

        use y * t; use (by simp)
        use x * t; use (by simp)
        use y * s; use (by simp)
        simp [hxy.symm, hst, tnz, ynz]
        constructor
        · intro heq
          rw [heq] at this
          simp at this
          have : S.card ≤ 2 := by rw [this]; exact Finset.card_le_two
          linarith
        · rw [show x * t * (y * s) = y * t * (x * s) by ring]
          simp

      -- case 2 : x * t ∉ S, we have y * s ∣ x * s * y * t
      by_cases hxt : x * t ∉ S
      · have h_S_subset' : S ⊆ {x * s, x * t, y * s, y * t} \ {x * t} := by
          refine Finset.subset_sdiff.mpr ?_
          constructor
          · exact h_S_subset
          exact Finset.disjoint_singleton_right.mpr hxt

        by_cases h' : x * t = y * s
        · have : {x * s, x * t, y * s, y * t} \ {x * t} = ({x * s, y * t} : Finset ℕ) := by
            ext z
            constructor
            · intro hz
              simp at hz
              rcases hz.1 with rfl | rfl | rfl |rfl
              all_goals simp [h'] at hz ⊢
            · intro hz
              simp at hz
              rcases hz with rfl | rfl
              · simp; use hst
              · simp; use hxy.symm
          rw [this] at h_S_subset'
          have : ({x * s, y * t} : Finset ℕ).card ≤ 2 := by exact Finset.card_le_two
          have : S.card ≤ 2 := by
            trans ({x * s, y * t} : Finset ℕ).card
            exact Finset.card_le_card h_S_subset'
            exact this
          linarith

        have : {x * s, x * t, y * s, y * t} \ {x * t} = ({x * s, y * s, y * t} : Finset ℕ) := by
          ext z
          constructor
          · intro hz
            simp at hz
            rcases hz.1 with rfl | rfl | rfl |rfl
            all_goals simp [h'] at hz ⊢
          · intro hz
            simp at hz
            rcases hz with rfl | rfl | rfl
            all_goals simp  [hst, hxy.symm]
            · exact xnz
            · exact fun x ↦ h' x.symm
            exact tnz
        rw [this] at h_S_subset'

        have : S = ({x * s, y * s, y * t} : Finset ℕ) := by
          apply Finset.eq_of_subset_of_card_le
          exact h_S_subset'
          trans 3
          exact Finset.card_le_three
          exact Nat.le_of_eq (id (Eq.symm hk_eq))
        rw [this]

        use y * s; use (by simp)
        use x * s; use (by simp)
        use y * t; use (by simp)
        simp [hxy.symm, hst.symm, tnz, ynz, snz, xnz]
        constructor
        · intro heq
          rw [heq] at this
          simp at this
          have : S.card ≤ 2 := by rw [this]; exact Finset.card_le_two
          linarith
        constructor
        · rw [show x * s * (y * t) = y * s * (x * t) by ring]

      -- case 3 : y * s ∉ S, we have x * t ∣ x * s * y * t
      by_cases hys : y * s ∉ S
      · have h_S_subset' : S ⊆ {x * s, x * t, y * s, y * t} \ {y * s} := by
          refine Finset.subset_sdiff.mpr ?_
          constructor
          · exact h_S_subset
          exact Finset.disjoint_singleton_right.mpr hys

        by_cases h' : y * s = x * t
        · have : {x * s, x * t, y * s, y * t} \ {y * s} = ({y * t, x * s} : Finset ℕ) := by
            ext z
            constructor
            · intro hz
              simp at hz
              rcases hz.1 with rfl | rfl | rfl |rfl
              all_goals simp [h'] at hz ⊢
            · intro hz
              simp at hz
              rcases hz with rfl | rfl
              · simp; use hst.symm
              · simp; use hxy
          rw [this] at h_S_subset'
          have : ({y * t, x * s} : Finset ℕ).card ≤ 2 := by exact Finset.card_le_two
          have : S.card ≤ 2 := by
            trans ({y * t, x * s} : Finset ℕ).card
            exact Finset.card_le_card h_S_subset'
            exact this
          linarith

        have : {x * s, x * t, y * s, y * t} \ {y * s} = ({x * t, x * s, y * t} : Finset ℕ) := by
          ext z
          constructor
          · intro hz
            simp at hz
            rcases hz.1 with rfl | rfl | rfl |rfl
            all_goals simp [h'] at hz ⊢
          · intro hz
            simp at hz
            rcases hz with rfl | rfl | rfl
            all_goals simp  [hst.symm, hxy]
            · exact fun x ↦ h' x.symm
            · exact snz
            · exact ynz
        rw [this] at h_S_subset'

        have : S = ({x * t, x * s, y * t} : Finset ℕ) := by
          apply Finset.eq_of_subset_of_card_le
          exact h_S_subset'
          trans 3
          exact Finset.card_le_three
          exact Nat.le_of_eq (id (Eq.symm hk_eq))
        rw [this]

        use x * t; use (by simp)
        use x * s; use (by simp)
        use y * t; use (by simp)
        simp [hxy.symm, hst.symm, tnz, xnz]
        constructor
        · intro heq
          rw [heq] at this
          simp at this
          have : S.card ≤ 2 := by rw [this]; exact Finset.card_le_two
          linarith
        · rw [show x * s * (y * t) = x * t * (y * s) by ring]
          simp

      -- case 4 : y * t ∉ S, we have x * s ∣ y * s * x * t
      by_cases hyt : y * t ∉ S
      · have h_S_subset' : S ⊆ {x * s, x * t, y * s, y * t} \ {y * t} := by
          refine Finset.subset_sdiff.mpr ?_
          constructor
          · exact h_S_subset
          exact Finset.disjoint_singleton_right.mpr hyt

        by_cases h' : y * t = x * s
        · have : {x * s, x * t, y * s, y * t} \ {y * t} = ({y * s, x * t} : Finset ℕ) := by
            ext z
            constructor
            · intro hz
              simp at hz
              rcases hz.1 with rfl | rfl | rfl |rfl
              all_goals simp [h'] at hz ⊢
            · intro hz
              simp at hz
              rcases hz with rfl | rfl
              · simp; use hst
              · simp; use hxy
          rw [this] at h_S_subset'
          have : ({y * s, x * t} : Finset ℕ).card ≤ 2 := by exact Finset.card_le_two
          have : S.card ≤ 2 := by
            trans ({y * s, x * t} : Finset ℕ).card
            exact Finset.card_le_card h_S_subset'
            exact this
          linarith

        have : {x * s, x * t, y * s, y * t} \ {y * t} = ({x * s, y * s, x * t} : Finset ℕ) := by
          ext z
          constructor
          · intro hz
            simp at hz
            rcases hz.1 with rfl | rfl | rfl |rfl
            all_goals simp [h'] at hz ⊢
          · intro hz
            simp at hz
            rcases hz with rfl | rfl | rfl
            all_goals simp  [hst, hxy]
            · exact fun x ↦ h' x.symm
            · exact ynz
            exact tnz
        rw [this] at h_S_subset'

        have : S = ({x * s, y * s, x * t} : Finset ℕ) := by
          apply Finset.eq_of_subset_of_card_le
          exact h_S_subset'
          trans 3
          exact Finset.card_le_three
          exact Nat.le_of_eq (id (Eq.symm hk_eq))
        rw [this]

        use x * s; use (by simp)
        use y * s; use (by simp)
        use x * t; use (by simp)
        simp [hxy, hst.symm, tnz, ynz, snz, xnz]
        constructor
        · intro heq
          rw [heq] at this
          simp at this
          have : S.card ≤ 2 := by rw [this]; exact Finset.card_le_two
          linarith
        constructor
        · rw [show y * s * (x * t) = x * s * (y * t) by ring]

      -- case 5, finally, all four multiples are in S, so there are redundents
      push_neg at hxs hys hxt hyt

      -- case 5.1, x * s = y * t, we have y * t ∣ x * t * y * s
      by_cases h1 : x * s = y * t
      · rw [h1] at h_S_subset
        simp at h_S_subset
        have : S = ({x * t, y * s, y * t} : Finset ℕ) := by
          apply Finset.eq_of_subset_of_card_le
          exact h_S_subset
          trans 3
          exact Finset.card_le_three
          exact Nat.le_of_eq (id (Eq.symm hk_eq))
        rw [this]

        use y * t; use (by simp)
        use x * t; use (by simp)
        use y * s; use (by simp)
        simp [hxy.symm, hst, tnz]
        constructor
        · intro heq
          rw [heq] at this
          simp at this
          have : S.card ≤ 2 := by rw [this]; exact Finset.card_le_two
          rw [hk_eq] at this
          norm_num at this
        use ynz
        · rw [show x * t * (y * s) = y * t * (x * s) by ring]
          apply dvd_mul_right

      -- case 5.2, y * s = x * t, we have x * t ∣ y * t * y * s
      by_cases h2 : y * s = x * t
      · rw [h2] at h_S_subset
        simp at h_S_subset
        have : S = ({x * s, x * t, y * t} : Finset ℕ) := by
          apply Finset.eq_of_subset_of_card_le
          exact h_S_subset
          trans 3
          exact Finset.card_le_three
          exact Nat.le_of_eq (id (Eq.symm hk_eq))
        rw [this]

        use x * t; use (by simp)
        use x * s; use (by simp)
        use y * t; use (by simp)
        simp [hxy.symm, hst.symm, tnz, xnz]
        constructor
        · intro heq
          rw [heq] at this
          simp at this
          have : S.card ≤ 2 := by rw [this]; exact Finset.card_le_two
          linarith
        · rw [show x * s * (y * t) = x * t * (y * s) by ring]
          simp

      -- case 5.3, there are no reducdent elements, this contradicts to |S| = 3, but
      -- we can still find x * t ∣ x * s * y * t
      use x * t; use hxt
      use x * s; use hxs
      use y * t; use hyt
      simp [h1, hst.symm, hxy.symm, xnz, tnz]
      rw [show x * s * (y * t) = x * t * (y * s) by ring]
      simp

    -- For the inductive step, suppose the thesis holds for some $k-1 \geq 3$.
    case succ k' hk ih =>
      -- Since $k=|A|+|B|-1 \geq 4$,
      have : S.card ≥ 4 := by rw [hk_eq]; linarith only [hk]
      -- we have that $\max (|A|,|B|) \geq 3$
      have h_A_or_B : A.card ≥ 3 ∨ B.card ≥ 3 := by
        by_contra! h
        rw [h₂] at this
        have : A.card + B.card - 1 ≤ 2 + 2 - 1 := by
          gcongr
          exact Nat.le_of_lt_succ h.1
          exact Nat.le_of_lt_succ h.2
        linarith

      -- WLOG assume $|B| \geq 3$.
      wlog h : B.card ≥ 3
      · have wh := this k k' hk ih B A S hB hA h₁ h₀ ?_ ?_ hk_eq (by assumption) h_A_or_B.symm ?_
        exact wh
        · rw [h₂, Nat.add_comm]
        · intro z zmem
          have ⟨a, amem, b, bmem, hz⟩ := h₃ z zmem
          use b, bmem, a, amem
          rwa [mul_comm]
        · simp [h] at h_A_or_B
          exact h_A_or_B

      -- Since the set $S$ consists of $k=|A|+|B|-1 > |A|$ elements, by pigeonhole principle
      -- there exists a number $x \in A$ which appears as the first of the two factors of at least two elements of $S$.
      let S_type := {z : ℕ // z ∈ S}
      let S' : Finset S_type := .univ

      have h_S'_card: S'.card = S.card := by
        symm
        apply Finset.card_bij ?_ ?_ ?_ ?_
        use fun z zmem ↦ ⟨z, zmem⟩
        · intros; simp [S']
        · intro a₁ ha₁ a₂ ha₂ heq
          exact Subtype.eq_iff.mp heq
        · intro ⟨z, zmem⟩ _
          use z
          use zmem

      let fst_fac : S_type → ℕ := fun ⟨z, zmem⟩ ↦ h₃ z zmem |>.choose

      have h_fst_fac_mem_A : ∀ z ∈ S', fst_fac z ∈ A := by
        intro ⟨z, zmem⟩ _
        generalize h : fst_fac ⟨z, zmem⟩ = a
        simp [fst_fac] at h
        have := Exists.choose_spec (h₃ z zmem)
        rw [h] at this
        exact this.1

      have h_card_mul_lt : A.card * 1 < S'.card := by
        simp
        rw [h_S'_card, h₂]
        rw [Nat.add_sub_assoc]
        refine Nat.lt_add_of_pos_right ?_
        exact Nat.zero_lt_sub_of_lt h₁
        exact Nat.one_le_of_lt h₁

      have ⟨x, xmem, hx⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to h_fst_fac_mem_A h_card_mul_lt

      let S_x := ({⟨z, zmem⟩ : S_type | ∃ y ∈ B, z = x * y} : Finset S_type)
      have h_filter : Finset.filter (fun x_1 ↦ fst_fac x_1 = x) S' ⊆ S_x := by
        intro ⟨z, zmem⟩ zmem'
        simp [fst_fac, S_x] at zmem' ⊢
        have := Exists.choose_spec (h₃ z zmem)
        rw [zmem'.2] at this
        exact this.2

      have : S_x.card > 1 := by
        calc
          S_x.card ≥ (Finset.filter (fun x_1 ↦ fst_fac x_1 = x) S').card := Finset.card_le_card h_filter
          _ > 1 := by exact hx

      -- So, there exist $y, z \in B$ with $x y, x z \in S$.
      have ⟨xy, xymem, xz, xzmem, hxy_xz⟩ := Finset.one_lt_card.mp this
      simp [S_x] at xymem xzmem
      have ⟨y, ymem, hy⟩ := xymem
      have ⟨z, zmem, hz⟩ := xzmem

      have ynz : y ≠ 0 := Nat.ne_zero_iff_zero_lt.mpr (hB y ymem)
      have znz : z ≠ 0 := Nat.ne_zero_iff_zero_lt.mpr (hB z zmem)

      -- If there exists $t \in A \setminus \{x\}$ such that $t y \in S$ and $t y \neq x z$,
      -- then we are done because $x y \mid x z \cdot t y$.
      by_cases ht : ∃ t ∈ A \ {x}, t * y ∈ S ∧ t * y ≠ x * z
      · have ⟨t, tmem, tymem, hty_xz⟩ := ht
        have tnex : t ≠ x := by intro h; rw [h] at tmem; simp at tmem
        use x * y; use (by rw [← hy]; simp)
        use x * z; use (by rw [← hz]; simp)
        use t * y; use tymem
        use (by rw [← hy, ← hz]; exact Subtype.coe_ne_coe.mpr hxy_xz)
        use hty_xz.symm
        use (by simp [ynz, tnex])
        rw [show x * z * (t * y) = x * y * (t * z) by ring]
        simp only [dvd_mul_right]

      -- If there exists no such $t$ then apply the inductive hypothesis to the sets $A$, $B \setminus \{y\}$ and $S \setminus \{x y\}$
      push_neg at ht
      let B' := B \ {y}
      have h_B'_card₀ : B'.card = B.card - 1 := by
        rw [show 1 = ({y} : Finset ℕ).card by exact rfl]
        refine Finset.card_sdiff ?_
        simp only [Finset.singleton_subset_iff, ymem]

      have h_B'_card: B'.card ≥ 2 := by
        rw [h_B'_card₀]
        exact Nat.le_sub_one_of_lt h

      have hB' : ∀ b ∈ B', b > 0 := by
        intro b bmem
        have : b ∈ B := by simp [B'] at bmem; exact bmem.1
        exact hB b this

      let S' := S \ {x * y}
      have : S'.card = S.card - 1 := by
        rw [show 1 = ({x * y} : Finset ℕ).card by exact rfl]
        refine Finset.card_sdiff ?_
        rw [Finset.singleton_subset_iff, ← hy]
        simp only [Finset.coe_mem]

      have h_S'_card : S'.card = k' := by
        rw [this, hk_eq]
        apply Nat.add_sub_cancel

      have h_S'_card_eq : S'.card = A.card + B'.card - 1 := by
        rw [this, h₂, h_B'_card₀, Nat.add_sub_assoc]
        exact Nat.one_le_of_lt h₁

      have h_S'_subset : S' ⊆ S := by
        exact Finset.sdiff_subset

      -- note here that every element of $S \setminus \{x y\}$ still has the form
      -- $a b$ for $a \in A$ and $b \in B \backslash\{y\}$.
      have h_S'_mem : ∀ x ∈ S', ∃ a ∈ A, ∃ b ∈ B', x = a * b := by
        intro z' z'mem
        have ⟨a, amem, b, bmem, hz'_eq⟩ := h₃ z' (h_S'_subset z'mem)
        by_cases hb : b ≠ y
        · have : b ∈ B' := by
            unfold B'
            apply Finset.mem_sdiff.mpr
            use bmem
            simp [hb]
          use a, amem, b, this
        push_neg at hb
        have : a ≠ x := by
          intro hax
          rw [hz'_eq, hb, hax] at z'mem
          simp [S'] at z'mem
        have : a ∈ A \ {x} := by
          simp [amem, this]
        have := ht a this (show a * y ∈ S by rw [← hb, ← hz'_eq]; exact h_S'_subset z'mem)
        use x, xmem, z
        constructor
        · simp [B', zmem]
          intro hzy
          have : xy.val ≠ xz.val := by exact Subtype.coe_ne_coe.mpr hxy_xz
          rw [hy, hz, hzy] at this
          exact this rfl
        · rwa [hz'_eq, hb]

      have ⟨x, xmem, y, ymem, z, zmem, hxy, hyz, hzx, hdvd⟩ :=
        ih A B' S' hA hB' h₀ h_B'_card h_S'_card_eq h_S'_mem h_S'_card

      use x, h_S'_subset xmem
      use y, h_S'_subset ymem
      use z, h_S'_subset zmem
