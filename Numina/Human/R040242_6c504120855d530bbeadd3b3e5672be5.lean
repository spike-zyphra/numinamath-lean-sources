import Mathlib
open Finset
set_option linter.unusedVariables false

/- 4. (HUN) Each of 17 students talked with every other student. They all talked about three different topics. Each pair of students talked about one topic. Prove that there are three students that talked about the same topic among themselves. -/
theorem combinatorics_24564 (a : Fin 17 → Fin 17 → Fin 3)
    (ha : ∀ i, a i i = 0) :
    ∃ b c d, b ≠ c ∧ b ≠ d ∧ c ≠ d ∧ a b c = a c d ∧ a c d = a b d := by
  -- Choose any student $A$, who has $16$ discussions.
  have h_card : ∀ A : Fin 17, Finset.card (Finset.univ \ {A}) = 16 := by
    intro A
    -- Calculate the number of students excluding $A$, which should be $16$.
    simp [Finset.card_univ, Finset.card_sdiff, Finset.card_singleton]
  -- Apply the pigeonhole principle: There exists a topic T with at least $6$ discussions.
  have h_pigeonhole : ∀ A : Fin 17, ∃ T : Fin 3, 6 ≤ Finset.card (Finset.filter (fun B => a A B = T) (Finset.univ \ {A})) := by
    intro A
    -- Prove that the total number of discussions across all topics $T$ is $16$.
    have h_sum : Finset.sum Finset.univ (fun T : Fin 3 => Finset.card (Finset.filter (fun B => a A B = T) (Finset.univ \ {A}))) = 16 := by
      -- Set decomposition: $univ \ {A}$ is partitioned into three disjoint subsets based on the value of $a A B$.
      have h_disjoint : ∀ T₁ ∈ univ, ∀ T₂ ∈ univ, T₁ ≠ T₂ → Disjoint (Finset.filter (fun B => a A B = T₁) (Finset.univ \ {A})) (Finset.filter (fun B => a A B = T₂) (Finset.univ \ {A})) := by
        intros T₁ _ T₂ _ hT
        rw [disjoint_iff_ne]
        intros x hx y hy h_eq
        simp [mem_filter] at hx hy
        have : a A x = T₁ ∧ a A x = T₂ := ⟨hx.2, by rw [h_eq]; exact hy.2⟩
        have h_eq_topics : T₁ = T₂ := this.1 ▸ this.2
        exact hT h_eq_topics
      -- Prove that the union of these subsets is $Finset.univ \ {A}$.
      have h_union : Finset.univ \ {A} = Finset.sup Finset.univ (fun T : Fin 3 => Finset.filter (fun B => a A B = T) (Finset.univ \ {A})) := by
        ext x
        simp only [mem_sdiff, mem_sup, mem_filter, mem_univ, true_and]
        apply Iff.intro
        · intro hx
          use a A x
        · intro ⟨T, hx⟩
          exact hx.1
      -- Calculate the cardinality.
      have h_card_eq : Finset.sum Finset.univ (fun T : Fin 3 => Finset.card (Finset.filter (fun B => a A B = T) (Finset.univ \ {A}))) = (Finset.univ \ {A}).card := by
        let t : Fin 3 → Finset (Fin 17) := fun T => Finset.filter (fun B => a A B = T) (Finset.univ \ {A})
        have : Finset.biUnion Finset.univ t = Finset.sup Finset.univ t := by rw [← Finset.sup_eq_biUnion]
        rw [← Finset.card_biUnion h_disjoint]
        rw [this]
        rw [h_union]
      rw [h_card_eq]
      have h_subset : {A} ⊆ univ := by simp [subset_univ]
      have h_card_sdiff : (univ \ {A}).card = univ.card - ({A} : Finset (Fin 17)).card := Finset.card_sdiff h_subset
      rw [h_card_sdiff]
      simp [Finset.card_univ, Finset.card_fin, Finset.card_singleton]
    -- Use proof by contradiction.
    by_contra! h_neg
    -- Convert the negation $<6$ to $≤5$.
    have h_neg' : ∀ T : Fin 3, Finset.card (Finset.filter (fun B => a A B = T) (Finset.univ \ {A})) ≤ 5 := by
      intro T
      exact Nat.le_of_lt_succ (h_neg T)
    -- Prove: Under the assumption, the total number of discussions is at most $15$.
    have h_sum_le : Finset.sum Finset.univ (fun T : Fin 3 => Finset.card (Finset.filter (fun B => a A B = T) (Finset.univ \ {A}))) ≤ 15 := by
      calc
        Finset.sum Finset.univ (fun T : Fin 3 => Finset.card (Finset.filter (fun B => a A B = T) (Finset.univ \ {A})))
        ≤ Finset.sum Finset.univ (fun _ => 5) := by
          -- For each topic $T$, the number of discussions is at most $5$.
          apply Finset.sum_le_sum
          intro T _
          exact h_neg' T
        _ = 3 * 5 := by
          -- The cardinality of Finset.univ : $Finset (Fin 3)$ is $3$.
          simp [Finset.sum_const, Finset.card_fin]
        _ = 15 := by norm_num
    -- Obtain contradiction: $16$ cannot be less than or equal to $15$.
    have h_contra : 16 ≤ 15 := by
      rw [← h_sum]
      exact h_sum_le
    exact Nat.not_le_of_gt (by norm_num) h_contra
  -- Select student $A$ and topic $T₃$, and obtain the corresponding student set $S₃$.
  obtain ⟨T₃, hT₃⟩ := h_pigeonhole 0
  let S₃ := Finset.filter (fun B => a 0 B = T₃) (Finset.univ \ {0})
  have hS₃_card : S₃.card ≥ 6 := hT₃

  -- Analyze the discussion situation in $S₃$.
  by_cases h_case1 : ∃ B ∈ S₃, ∃ C ∈ S₃, B ≠ C ∧ a B C = T₃
  · -- Case $1$: There exist $B$, $C$ in $S₃$ discussing $T₃$.
    obtain ⟨B, hB_mem, C, hC_mem, hBC_ne, hBC⟩ := h_case1
    have hB_ne_0 : B ≠ 0 := by simp [S₃, mem_filter] at hB_mem; exact hB_mem.1
    have hC_ne_0 : C ≠ 0 := by simp [S₃, mem_filter] at hC_mem; exact hC_mem.1
    have h_abc : a 0 B = a B C := by
      have : a 0 B = T₃ := (mem_filter.mp hB_mem).2
      rw [this, hBC]
    have h_bcd : a B C = a 0 C := by
      have : a 0 C = T₃ := (mem_filter.mp hC_mem).2
      rw [hBC, this]
    use 0, B, C
    exact ⟨Ne.symm hB_ne_0, Ne.symm hC_ne_0, hBC_ne, h_abc, h_bcd⟩

  · -- Case $2$: No two students in $S₃$ discuss $T₃$.
    have h_no_T₃ : ∀ x ∈ S₃, ∀ y ∈ S₃, x ≠ y → a x y ≠ T₃ := by
      intro B hB C hC hBC
      by_contra h_contr
      apply h_case1
      exact ⟨B, hB, C, hC, hBC, h_contr⟩

    -- Select $B ∈ S₃$ and apply the pigeonhole principle.
    have hS₃_nonempty : S₃.Nonempty := by
      exact card_pos.mp (by linarith [hS₃_card])
    obtain ⟨B, hB_mem⟩ := hS₃_nonempty
    have hB_ne_0 : B ≠ 0 := by simp [S₃, mem_filter] at hB_mem; exact hB_mem.1

    -- $B$ discusses with other students in $S₃$, with at least $5$ students remaining after excluding $B$.
    let S₃_minus_B := filter (fun C => C ≠ B) S₃
    have hS₃_minus_B_card : card S₃_minus_B ≥ 5 := by
      have hB_in_S₃ : B ∈ S₃ := hB_mem
      have h_eq : S₃_minus_B = S₃ \ {B} := by
        ext x
        simp [S₃_minus_B, mem_filter, mem_sdiff, mem_singleton]
      rw [h_eq]
      simp [card_sdiff (singleton_subset_iff.mpr hB_in_S₃), card_singleton, hS₃_card]
      omega

    have h_pigeon_B : ∃ T : Fin 3, T ≠ T₃ ∧ 3 ≤ card (filter (fun C => a B C = T) S₃_minus_B) := by
      have h_sum_B : Finset.sum univ (fun T : Fin 3 => card (filter (fun C => a B C = T) S₃_minus_B)) = card S₃_minus_B := by
        -- Prove that the subsets are pairwise disjoint.
        have h_disjoint_B : ∀ T₁ ∈ univ, ∀ T₂ ∈ univ, T₁ ≠ T₂ → Disjoint (filter (fun C => a B C = T₁) S₃_minus_B) (filter (fun C => a B C = T₂) S₃_minus_B) := by
          intros T₁ _ T₂ _ hT
          rw [disjoint_iff_ne]
          intros x hx y hy h_eq
          simp [mem_filter] at hx hy
          have : a B x = T₁ ∧ a B x = T₂ := ⟨hx.2, by rw [h_eq]; exact hy.2⟩
          have h_eq_topics : T₁ = T₂ := this.1 ▸ this.2
          exact hT h_eq_topics
        -- Prove that the union equals $S₃_minus_B$.
        have h_union_B : S₃_minus_B = Finset.sup univ (fun T : Fin 3 => filter (fun C => a B C = T) S₃_minus_B) := by
          ext x
          simp only [mem_sup, mem_filter]
          constructor
          · intro hx
            use a B x
            simp [hx]
          · intro ⟨T, hx⟩
            exact hx.2.1
        -- Calculate the cardinality.
        have h_card_eq : Finset.sum univ (fun T : Fin 3 => card (filter (fun C => a B C = T) S₃_minus_B)) = card S₃_minus_B := by
          let t : Fin 3 → Finset (Fin 17) := fun T => filter (fun C => a B C = T) S₃_minus_B
          have : Finset.biUnion Finset.univ t = Finset.sup Finset.univ t := by rw [← Finset.sup_eq_biUnion]
          rw [← Finset.card_biUnion h_disjoint_B]
          rw [this]
          rw [h_union_B]
        rw [h_card_eq]
      by_contra! h_neg
      have h_neg' : ∀ T : Fin 3, T ≠ T₃ → card (filter (fun C => a B C = T) S₃_minus_B) ≤ 2 := by
        intro T hT; exact Nat.le_of_lt_succ (h_neg T hT)
      have h_sum_le : Finset.sum univ (fun T : Fin 3 => card (filter (fun C => a B C = T) S₃_minus_B)) ≤ 4 := by
        calc
          Finset.sum (univ : Finset (Fin 3)) (fun T => card (filter (fun C => a B C = T) S₃_minus_B))
          = Finset.sum (univ \ {T₃}) (fun T => card (filter (fun C => a B C = T) S₃_minus_B)) +
            Finset.sum ({T₃}) (fun T => card (filter (fun C => a B C = T) S₃_minus_B)) := by
            have : {T₃} ⊆ univ := by intro x hx; simp [mem_singleton] at hx; simp [hx]
            rw [Finset.sum_sdiff this]
          _ = Finset.sum (univ \ {T₃}) (fun T => card (filter (fun C => a B C = T) S₃_minus_B)) +
            card (filter (fun C => a B C = T₃) S₃_minus_B) := by rw [Finset.sum_singleton]
          _ ≤ Finset.sum (univ \ {T₃}) (fun _ => 2) + 0 := by
            apply add_le_add
            · apply Finset.sum_le_sum
              intro T hT
              exact h_neg' T (by simp [mem_sdiff] at hT; exact hT)
            · have h_T₃_empty : filter (fun C => a B C = T₃) S₃_minus_B = ∅ := by
                ext x
                simp [mem_filter]
                intro h_x h_a
                have h_x_in_S₃ : x ∈ S₃ := by
                  simp [S₃_minus_B, mem_filter] at h_x
                  exact h_x.1
                have h_x_ne_B : x ≠ B := by
                  simp [S₃_minus_B, mem_filter] at h_x
                  exact h_x.2
                have : a B x ≠ T₃ := h_no_T₃ B hB_mem x h_x_in_S₃ h_x_ne_B.symm
                contradiction
              rw [h_T₃_empty]
              simp
          _ = 2 * (univ \ {T₃}).card := by rw [Finset.sum_const];ring
          _ = 2 * 2 := by
            simp [card_sdiff, card_singleton, card_fin]
          _ = 4 := by norm_num
      have : card S₃_minus_B ≤ 4 := by rw [← h_sum_B]; exact h_sum_le
      linarith [hS₃_minus_B_card]

    obtain ⟨T₂, hT₂_ne_T₃, hT₂_card⟩ := h_pigeon_B
    let S₂ := filter (fun C => a B C = T₂) S₃_minus_B

    -- $S₂$ has at least $3$ students, analyze two cases.
    have hS₂_card : card S₂ ≥ 3 := hT₂_card
    -- Since card $S₂ ≥ 3$, there exist $C, D, E ∈ S₂$, with $C ≠ D$, $C ≠ E$, $D ≠ E$.
    have : card S₂ ≥ 3 → ∃ C ∈ S₂, ∃ D ∈ S₂, ∃ E ∈ S₂, C ≠ D ∧ C ≠ E ∧ D ≠ E := by
      intro h
      obtain ⟨C, hC⟩ := card_pos.mp (by linarith [h])
      have : card (S₂ \ {C}) ≥ 2 := by
        rw [Finset.card_sdiff (singleton_subset_iff.mpr hC)]
        simp only [Finset.card_singleton]
        have : card S₂ ≥ 3 := h
        have : card S₂ - 1 ≥ 2 := by omega
        exact this
      obtain ⟨D, hD⟩ := card_pos.mp (by linarith [this])
      have : card ((S₂ \ {C}) \ {D}) ≥ 1 := by
        rw [Finset.card_sdiff (singleton_subset_iff.mpr hD)]
        simp only [Finset.card_singleton]
        have : card (S₂ \ {C}) ≥ 2 := by
          rw [Finset.card_sdiff (singleton_subset_iff.mpr hC)]
          simp only [Finset.card_singleton]
          have : card S₂ - 1 ≥ 2 := by omega
          exact this
        have : card (S₂ \ {C}) - 1 ≥ 1 := by omega
        exact this
      obtain ⟨E, hE⟩ := card_pos.mp (by linarith [this])
      use C, hC, D
      simp [mem_sdiff, mem_singleton] at hD hE
      use hD.1, E
      use hE.1.1
      tauto
    -- List conditions for $C, D, E$ being pairwise distinct and related to $S₃$.
    obtain ⟨C, hC_mem, D, hD_mem, E, hE_mem, hC_ne_D, hC_ne_E, hD_ne_E⟩ := this hS₂_card
    have hC_in_S₃_minus_B : C ∈ S₃_minus_B := by exact (mem_filter.mp hC_mem).1
    have h_aBC : a B C = T₂ := by exact (mem_filter.mp hC_mem).2
    have hC_in_S₃ : C ∈ S₃ := by exact (mem_filter.mp hC_in_S₃_minus_B).1
    have hC_ne_B : C ≠ B := by exact (mem_filter.mp hC_in_S₃_minus_B).2
    have hD_in_S₃_minus_B : D ∈ S₃_minus_B := by exact (mem_filter.mp hD_mem).1
    have h_aBD : a B D = T₂ := by exact (mem_filter.mp hD_mem).2
    have hD_in_S₃ : D ∈ S₃ := by exact (mem_filter.mp hD_in_S₃_minus_B).1
    have hD_ne_B : D ≠ B := by exact (mem_filter.mp hD_in_S₃_minus_B).2
    have hE_in_S₃_minus_B : E ∈ S₃_minus_B := by exact (mem_filter.mp hE_mem).1
    have h_aBE : a B E = T₂ := by exact (mem_filter.mp hE_mem).2
    have hE_in_S₃ : E ∈ S₃ := by exact (mem_filter.mp hE_in_S₃_minus_B).1
    have hE_ne_B : E ≠ B := by exact (mem_filter.mp hE_in_S₃_minus_B).2
    by_cases h_T₂ : a C D = T₂ ∨ a C E = T₂ ∨ a D E = T₂
    -- Case $1$: At least one pair discusses $T₂$, forming a trio with $B$.
    ·   cases h_T₂ with
      | inl h_aCD_T₂ =>
        -- Subcase $1$: $a C D = T₂$.
        use B, C, D
        exact ⟨Ne.symm hC_ne_B, Ne.symm hD_ne_B, hC_ne_D, by rw [h_aBC, h_aCD_T₂], by rw [h_aCD_T₂, h_aBD]⟩
      | inr h_rest =>
        cases h_rest with
        | inl h_aCE_T₂ =>
          -- Subcase $2$: $a C E = T₂$.
          use B, C, E
          exact ⟨Ne.symm hC_ne_B, Ne.symm hE_ne_B, hC_ne_E, by rw [h_aBC, h_aCE_T₂], by rw [h_aCE_T₂, h_aBE]⟩
        | inr h_aDE_T₂ =>
          -- Subcase $3$: $a D E = T₂$.
          use B, D, E
          exact ⟨Ne.symm hD_ne_B, Ne.symm hE_ne_B, hD_ne_E, by rw [h_aBD, h_aDE_T₂], by rw [h_aDE_T₂, h_aBE]⟩
    · -- Case $2$: $a C D ≠ T₂ ∧ a C E ≠ T₂ ∧ a D E ≠ T₂$, then $C, D, E$ form a trio.
      have h_no_T₂ : a C D ≠ T₂ ∧ a C E ≠ T₂ ∧ a D E ≠ T₂ := by tauto
      have h_aCD_ne_T₃ : a C D ≠ T₃ := by exact h_no_T₃ C hC_in_S₃ D hD_in_S₃ hC_ne_D
      have h_aCE_ne_T₃ : a C E ≠ T₃ := by exact h_no_T₃ C hC_in_S₃ E hE_in_S₃ hC_ne_E
      have h_aDE_ne_T₃ : a D E ≠ T₃ := by exact h_no_T₃ D hD_in_S₃ E hE_in_S₃ hD_ne_E
      -- Assume $T₁ ∈ Fin 3 \ {T₂, T₃}$.
      have h_T₁ : ∃ T₁ ∈ Finset.univ, T₁ ≠ T₂ ∧ T₁ ≠ T₃ := by
        have h_nonempty : (Finset.univ \ {T₂, T₃} : Finset (Fin 3)).Nonempty := by
          have h₁: (Finset.univ : Finset (Fin 3)).card = 3 := Finset.card_fin 3
          have h₂: Finset.card {T₂, T₃} = 2 := by simp [hT₂_ne_T₃]
          have h₃: (Finset.univ \ {T₂, T₃} : Finset (Fin 3)).card = 3 - Finset.card {T₂, T₃} := by
            simp [Finset.card_sdiff]
          have : (Finset.univ \ {T₂, T₃} : Finset (Fin 3)).card = 1 := by simp only [h₃, h₂]
          apply Finset.card_pos.mp (by nlinarith [this])
        obtain ⟨T₁, hT₁⟩ := h_nonempty
        use T₁
        have hT₁' : T₁ ∈ Finset.univ ∧ T₁ ≠ T₂ ∧ T₁ ≠ T₃ := by
          simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at hT₁
          exact ⟨hT₁.1, hT₁.2⟩
        exact ⟨hT₁'.1, hT₁'.2⟩
      obtain ⟨T₁, hT₁_mem, hT₁_ne_T₂, hT₁_ne_T₃⟩ := h_T₁
      -- $C, D, E$ all discuss $T₁$.
      have h_T₁_only : ∀ x : Fin 3, x ∈ Finset.univ → x ≠ T₂ → x ≠ T₃ → x = T₁ := by
        intros x _ hx_ne_T₂ hx_ne_T₃
        by_contra hx_ne_T₁
        -- For any topic $x$, $x ≠ T₁$, $x ≠ T₂$, $x ≠ T₃$ is impossible in Fin $3$.
        have h_fin3_exhaust : x = T₁ ∨ x = T₂ ∨ x = T₃ := by
          have h_fin3_vals : (Finset.univ : Finset (Fin 3)) = {T₁, T₂, T₃} := by
            apply Finset.eq_of_subset_of_card_le
            · intro y hy
              have h_card_eq : Finset.card {T₁, T₂, T₃} = 3 := by
                rw [Finset.card_insert_of_not_mem]
                · rw [Finset.card_insert_of_not_mem]
                  · simp [Finset.card_singleton]
                  · simp [hT₂_ne_T₃]
                · simp [hT₁_ne_T₂, hT₁_ne_T₃]
              have h_subset : {T₁, T₂, T₃} ⊆ Finset.univ := by
                simp [Finset.subset_iff, Finset.mem_univ]
              have h_eq_univ : {T₁, T₂, T₃} = Finset.univ := by
                apply Finset.eq_of_subset_of_card_le
                · exact h_subset
                · simp [Finset.card_univ, h_card_eq]
              rw [h_eq_univ]
              exact Finset.mem_univ y
            · have h_card_insert : Finset.card ({T₁, T₂, T₃} : Finset (Fin 3)) = 3 := by
                rw [Finset.card_insert_of_not_mem]
                · rw [Finset.card_insert_of_not_mem]
                  · simp [Finset.card_singleton]
                  · simp [hT₂_ne_T₃]
                · simp [hT₁_ne_T₂, hT₁_ne_T₃]
              simp [Finset.card_univ, h_card_insert]
          have h_x_in : x ∈ Finset.univ := by simp [Finset.mem_univ]
          rw [h_fin3_vals] at h_x_in
          simp [Finset.mem_insert, Finset.mem_singleton] at h_x_in
          exact h_x_in
        cases h_fin3_exhaust with
        | inl h_x_T₁ => contradiction
        | inr h_rest =>
          cases h_rest with
          | inl h_x_T₂ => contradiction
          | inr h_x_T₃ => contradiction
      -- Construct the trio $C, D, E$ discussing $T₁$ to satisfy the conditions.
      have h_aCD_T₁ : a C D = T₁ := by
        have h_fin3 : a C D ∈ Finset.univ := by simp [Finset.mem_univ]
        have h_not_T₂ : a C D ≠ T₂ := h_no_T₂.1
        have h_not_T₃ : a C D ≠ T₃ := h_aCD_ne_T₃
        exact h_T₁_only (a C D) h_fin3 h_not_T₂ h_not_T₃
      have h_aCE_T₁ : a C E = T₁ := by
        have h_fin3 : a C E ∈ Finset.univ := by simp [Finset.mem_univ]
        exact h_T₁_only (a C E) h_fin3 h_no_T₂.2.1 h_aCE_ne_T₃
      have h_aDE_T₁ : a D E = T₁ := by
        have h_fin3 : a D E ∈ Finset.univ := by simp [Finset.mem_univ]
        exact h_T₁_only (a D E) h_fin3 h_no_T₂.2.2 h_aDE_ne_T₃
      use C, D, E
      exact ⟨hC_ne_D, hC_ne_E, hD_ne_E, by rw [h_aCD_T₁,h_aDE_T₁], by rw [h_aDE_T₁, h_aCE_T₁]⟩
