import Mathlib

theorem inequalities_163453 :
    Set.ncard {p : ℤ × ℤ | (|p.1| - 1)^2 + (|p.2| - 1)^2 < 2} = 16 := by
  let P := {p : ℤ × ℤ | (|p.1| - 1)^2 + (|p.2| - 1)^2 < 2}
  let U : Finset <| ℤ × ℤ := Finset.Icc (-2) 2 ×ˢ Finset.Icc (-2) 2
  -- We can use the fact that the set of integer points in a circle is finite.
  -- Convert to finset
  have hU {x : ℤ × ℤ} : x ∈ P → x ∈ U := by
    intro hP
    simp [P] at hP
    simp [U]
    constructor
    · have : (|x.1| - 1) ^ 2 < 4 := by nlinarith only [hP]
      have : |x.1| < 3 := by nlinarith only [this]
      simp [abs] at this
      obtain ⟨h₁, h₂⟩ := this
      constructor
      all_goals linarith only [h₁, h₂]
    · have : (|x.2| - 1) ^ 2 < 4 := by nlinarith only [hP]
      have : |x.2| < 3 := by nlinarith only [this]
      simp [abs] at this
      obtain ⟨h₁, h₂⟩ := this
      constructor
      all_goals linarith only [h₁, h₂]
  -- by case analysis
  -- We can split the set into three parts according to x positive, zero and negative
  let P_pos : Finset <| ℤ × ℤ := U.filter (fun p => p ∈ P ∧ p.1 > 0)
  let P_zero : Finset <| ℤ × ℤ := U.filter (fun p => p ∈ P ∧ p.1 = 0)
  let P_neg : Finset <| ℤ × ℤ := U.filter (fun p => p ∈ P ∧ p.1 < 0)
  have P_pos_union_P_neg : P = P_pos ∪ P_zero ∪ P_neg := by
    ext ⟨x, y⟩
    simp [P_pos, P_zero, P_neg]
    constructor <;> intro h
    · simp [h, hU h]
      by_cases hx : x = 0
      · simp [hx]
      · rcases lt_or_gt_of_ne hx with h | h
        all_goals simp [h]
    · rcases h with h | h | h <;> exact h.2.1
  change Set.ncard P = _
  rw [P_pos_union_P_neg, Set.ncard_coe_Finset]
  rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
  · -- positive and negative parts have the same cardinality
    have P_pos_card_eq : P_pos.card = P_neg.card := by
      let f (p : ℤ × ℤ) := (-p.1, p.2)
      apply Finset.card_bijective f
      · constructor
        · intro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h
          simp [f] at h
          exact Prod.mk.inj_iff.mpr h
        · intro ⟨x, y⟩
          use ⟨-x, y⟩
          simp [f]
      · simp [P_pos, P_neg, P, U]
        intro _ _ _ _ _ _
        constructor <;> intro ⟨h₁, h₂⟩
        all_goals
          constructor
          all_goals linarith only [h₁, h₂]
    -- positive part has 7 elements
    have P_pos_card_eq' : P_pos.card = 7 := by
      -- We then split the positive part into three parts according to y positive, zero and negative
      let P_pos_y_pos : Finset <| ℤ × ℤ := P_pos.filter (fun p => p.2 > 0)
      let P_pos_y_zero : Finset <| ℤ × ℤ := P_pos.filter (fun p => p.2 = 0)
      let P_pos_y_neg : Finset <| ℤ × ℤ := P_pos.filter (fun p => p.2 < 0)
      have : P_pos = P_pos_y_pos ∪ P_pos_y_zero ∪ P_pos_y_neg := by
        ext ⟨x, y⟩
        simp [P_pos_y_pos, P_pos_y_zero, P_pos_y_neg]
        constructor <;> intro h
        · simp [h]
          by_cases hy : y = 0
          · simp [hy]
          · rcases lt_or_gt_of_ne hy with h | h
            all_goals simp [h]
        · rcases h with h | h | h <;> exact h.1
      rw [this, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
      · -- the positive part has 3 elements
        have P_pos_y_pos_card_eq : P_pos_y_pos.card = 3 := by
          have : P_pos_y_pos = {(1, 1), (1, 2), (2, 1)} := by
            ext ⟨x, y⟩
            unfold P_pos_y_pos P_pos P U
            simp
            constructor <;> intro h
            · obtain ⟨⟨⟨⟨_, hx'⟩, _, hy'⟩, ⟨h, hx⟩⟩, hy⟩ := h
              interval_cases x
              all_goals
                interval_cases y
                all_goals
                  simp at h ⊢
            · rcases h with h | h | h
              all_goals simp [h.1, h.2]
          rw [this]
          apply Finset.card_eq_three.mpr
          use (1, 1), (1, 2), (2, 1)
          simp
          constructor
          · exact ne_of_beq_false rfl
          · exact ne_of_beq_false rfl
        -- zero part has 1 element
        have y_zero_card_eq : P_pos_y_zero.card = 1 := by
          have : P_pos_y_zero = {(1, 0)} := by
            ext ⟨x, y⟩
            unfold P_pos_y_zero P_pos P U
            simp
            intro hy
            constructor <;> intro h
            · simp [hy] at h
              obtain ⟨⟨_, h₀⟩, h₁, h₂⟩ := h
              interval_cases x
              all_goals simp at h₁ ⊢
            · simp [h, hy]
          simp [this]
        -- negative part and positive part have the same cardinality
        have : P_pos_y_pos.card = P_pos_y_neg.card := by
          let f (p : ℤ × ℤ) : ℤ × ℤ := (p.1, -p.2)
          apply Finset.card_bijective f
          · simp [f]
            constructor
            · intro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h
              simp at h
              exact Prod.mk.inj_iff.mpr h
            · intro ⟨x, y⟩
              use ⟨x, -y⟩
              simp
          · simp [P_pos_y_pos, P_pos_y_neg, P_pos, f, P, U]
            intro _ _ _ _ _ _ _
            constructor <;> intro ⟨h₁, h₂⟩
            · constructor
              all_goals linarith only [h₁, h₂]
            · constructor
              all_goals linarith only [h₁, h₂]
        rw [←this, P_pos_y_pos_card_eq, y_zero_card_eq]
      · -- positive and zero parts are disjoint
        apply Finset.disjoint_left.mpr
        simp [P_pos_y_pos, P_pos_y_zero]
        intro x y hu hp
        simp [hu, hp]
        exact ne_of_gt hp
      · -- all three parts are disjoint
        rw [Finset.disjoint_union_left]
        constructor
        · apply Finset.disjoint_left.mpr
          simp [P_pos_y_zero, P_pos_y_neg, P_pos_y_pos, P_pos]
          intro x y hu hp
          simp [hu, hp]
          intro hx hy
          simp [hx]
          exact le_of_lt hy
        · apply Finset.disjoint_left.mpr
          simp [P_pos_y_zero, P_pos_y_neg, P_pos]
          intro x y hu hp
          simp [hu, hp]
          intro hx hy
          simp [hx, hy]
    -- zero part has 2 elements
    have P_zero_card_eq : P_zero.card = 2 := by
      have : P_zero = {(0, 1), (0, -1)} := by
        ext ⟨x, y⟩
        simp [P_zero, U, P]
        constructor <;> intro h
        · obtain ⟨⟨_, ⟨h₀, h₁⟩⟩, h₂, h₃⟩ := h
          simp [h₃] at h₂ ⊢
          interval_cases y
          all_goals simp at h₂ ⊢
        · rcases h with h | h
          all_goals simp [h]
      simp [this]
    rw [←P_pos_card_eq, P_pos_card_eq', P_zero_card_eq]
  · -- positive and zero parts are disjoint
    apply Finset.disjoint_left.mpr
    simp [P_pos, P_zero]
    intro x y hu hp
    simp [hu, hp]
    intro hgt
    exact ne_of_gt hgt
  · -- all three parts are disjoint
    rw [Finset.disjoint_union_left]
    constructor
    · apply Finset.disjoint_left.mpr
      simp [P_pos, P_neg]
      intro x y hu hp
      simp [hu, hp]
      intro hgt
      exact le_of_lt hgt
    · apply Finset.disjoint_left.mpr
      simp [P_zero, P_neg]
      intro x y hu hp
      simp [hu, hp]
      intro h
      simp [h]
