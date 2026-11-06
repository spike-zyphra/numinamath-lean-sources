import Mathlib

theorem algebra_180979 :
  (∀ m : ℝ, (∃ (S : Set (ℝ × ℝ)), Set.Infinite S ∧ ∀ (x y : ℝ), (x, y) ∈ S ↔ 2 * x + (m - 1) * y = 3 ∧ (m + 1) * x + 4 * y = -3) ↔ m = -3) ∧
  (∀ m : ℝ, (¬∃ (x y : ℝ), 2 * x + (m - 1) * y = 3 ∧ (m + 1) * x + 4 * y = -3) ↔ m = 3) := by
  -- First define the system of equations
  let system (m x y : ℝ) : Prop := 2 * x + (m - 1) * y = 3 ∧ (m + 1) * x + 4 * y = -3

  -- Define the predicate for the system having infinite solutions
  let hasInfiniteSolutions (m : ℝ) : Prop :=
    ∃ (S : Set (ℝ × ℝ)), Set.Infinite S ∧ ∀ (x y : ℝ), (x, y) ∈ S ↔ system m x y

  -- Define the predicate for the system having no solutions
  let hasNoSolutions (m : ℝ) : Prop := ¬∃ (x y : ℝ), system m x y

  -- Prove the two parts of the theorem
  constructor

  -- First theorem: the system has infinite solutions if and only if m = -3
  · intro m
    constructor

    -- Direction 1: If the system has infinite solutions, then m = -3
    · intro h_infinite_sols
      -- Here we prove: from hasInfiniteSolutions m we derive m = -3

      -- If there are infinite solutions, then there exist two solutions x1, y1 and x2, y2 such that
      -- 2 * x1 + (m - 1) * y1 = 3
      -- 2 * x2 + (m - 1) * y2 = 3
      -- 2 * x1 + (m + 1) * y1 = -3
      -- 2 * x2 + (m + 1) * y2 = -3

      -- Extract two distinct solutions from the infinite solution set
      have h_two_distinct_solutions : ∃ (x₁ y₁ x₂ y₂ : ℝ),
        (x₁ ≠ x₂ ∨ y₁ ≠ y₂) ∧
        system m x₁ y₁ ∧ system m x₂ y₂ := by
        -- Extract the infinite solution set S
        rcases h_infinite_sols with ⟨S, h_S_infinite, h_S_iff⟩

        have s_nontrivial : S.Nontrivial := Set.Infinite.nontrivial h_S_infinite
        -- Property of finite sets: any finite set is either empty or has a finite number of elements
        -- In particular, if all points in set S are the same, then S is a singleton set, and thus finite
        -- Therefore, since S is an infinite set, it must contain at least two different points

        obtain ⟨⟨x₁, y₁⟩, ⟨x₂, y₂⟩, h_neq, h_in⟩ := Set.Nontrivial.pair_subset s_nontrivial
        use x₁, y₁, x₂, y₂
        unfold system

        have h_x1y1_in_S : (x₁, y₁) ∈ S := by
          apply h_in
          exact Set.mem_insert (x₁, y₁) {(x₂, y₂)}
        have h_x2y2_in_S : (x₂, y₂) ∈ S := by
          apply h_in
          simp

        have h1:= (h_S_iff x₁ y₁).mp h_x1y1_in_S
        have h2:= (h_S_iff x₂ y₂).mp h_x2y2_in_S

        constructor
        . contrapose! h_neq
          rw [Prod.ext_iff]
          simp only [sub_eq_zero, eq_iff_iff]
          exact h_neq
        . exact ⟨h1, h2⟩


      -- Extract the differences dx and dy from the two distinct solutions
      have h_nonzero_differences : ∃ (dx dy : ℝ),
        (dx ≠ 0 ∨ dy ≠ 0) ∧
        2 * dx + (m - 1) * dy = 0 ∧
        (m + 1) * dx + 4 * dy = 0 := by
        obtain ⟨x₁, y₁, x₂, y₂, h_distinct, h_system₁, h_system₂⟩ := h_two_distinct_solutions
        let dx := x₁ - x₂
        let dy := y₁ - y₂
        have h_dx : dx = x₁ - x₂ := by rfl
        have h_dy : dy = y₁ - y₂ := by rfl
        use dx, dy
        rw [h_dx, h_dy]
        constructor
        . simp only [sub_ne_zero]
          exact h_distinct
        · unfold system at h_system₁ h_system₂
          have eq1 :  2 * x₁ + (m - 1) * y₁ = 2 * x₂ + (m - 1) * y₂ := by
            rw [h_system₁.1,h_system₂.1]
          have eq2 : (m + 1) * x₁ + 4 * y₁ = (m + 1) * x₂ + 4 * y₂ := by
            rw [h_system₁.2,h_system₂.2]

          constructor
          · linear_combination eq1
          · linear_combination eq2

      have h_determinant_zero : 9 - m ^ 2 = 0 := by
        obtain ⟨dx, dy, ⟨h1, h2, h3⟩⟩ := h_nonzero_differences
        have h_dx : dx = -(m - 1) * dy/2 := by
          rw [add_eq_zero_iff_eq_neg] at h2
          have h_dx : dx = 2 * dx /2 := by ring
          rw [h_dx, h2]
          ring

        have h_dy : dy = -(m+1)*dx/4 := by
          rw [add_comm, add_eq_zero_iff_eq_neg] at h3
          have h_dy : dy = 4 * dy /4 := by ring
          rw [h_dy, h3]
          ring

        have h3y : -(m ^ 2 * dy) + dy * 9 = 0:= by
          rw [h_dx] at h3
          field_simp at h3
          ring_nf at h3
          exact h3

        have h2x : dx * 9 - dx * m ^ 2 = 0 := by
          rw [h_dy] at h2
          field_simp at h2
          ring_nf at h2
          exact h2

        cases' h1 with h1_dx_zero h1_dy_zero
        · have : dx * 9 - dx * m ^ 2 = dx * (9 - m ^ 2) := by ring
          rw [this] at h2x
          have : dx * (9 - m ^ 2)/ dx = (9 - m ^ 2) := by field_simp
          rw [h2x] at this
          ring_nf at this
          exact this.symm
        · have :-(m ^ 2 * dy) + dy * 9 = (9-m^2)*dy := by ring
          rw [this] at h3y
          have : 9 - m ^ 2 = (9 - m ^ 2) * dy / dy := by
            field_simp
          rw [this, h3y]
          field_simp

      -- From m² = 9, we get m = 3 or m = -3
      have h_m_eq_3_or_neg3 : m = 3 ∨ m = -3 := by
        have : 9 - m ^ 2 = (3 - m) * (3 + m) := by ring
        rw [this, mul_eq_zero] at h_determinant_zero
        cases' h_determinant_zero with h1 h2
        . rw [sub_eq_zero] at h1
          exact Or.inl h1.symm
        . rw [add_comm, add_eq_zero_iff_eq_neg] at h2
          exact Or.inr h2

      -- Prove that m ≠ 3, because when m = 3, the system has no solutions, which contradicts our assumption
      have h_m_neq_3 : m ≠ 3 := by
        by_contra h_m_eq_3
        rw [h_m_eq_3] at h_infinite_sols
        ring_nf at h_infinite_sols
        -- contrapose! h_infinite_sols
        -- intro S S_infinite
        -- use 3/2, 0
        -- right
        -- ring_nf
        obtain ⟨S, S_infinite, h_system⟩ := h_infinite_sols
        have : ∀ (x y : ℝ), ¬ ( x * 2 + y * 2 = 3 ∧ x * 4 + y * 4 = -3) := by
          intro x y
          push_neg
          intro h
          have h_eq_1 : x * 4 + y * 4 = 2 * (x * 2 + y * 2) := by ring
          rw [h_eq_1, h]
          linarith

        have h_S_empty : S = ∅ := by
          ext ⟨x, y⟩
          rw [Set.mem_empty_iff_false, h_system]
          rw [iff_false]
          exact this x y

        have := Set.Infinite.nonempty S_infinite
        rw [h_S_empty] at this
        exact Set.not_nonempty_empty this

      -- Combining the above conclusions, we get m = -3
      have h_m_eq_neg3 : m = -3 := by
        cases' h_m_eq_3_or_neg3 with h1 h2
        · contradiction
        · exact h2
      -- Final result
      exact h_m_eq_neg3

    -- Direction 2: If m = -3, then the system has infinite solutions
    · intro h_m_eq_neg3
      -- Here we prove: from m = -3 we derive hasInfiniteSolutions m

      -- Proof strategy:
      -- 1. Substitute m = -3 into the system of equations:
      --    2x + (-3-1)y = 3  ⟹  2x - 4y = 3
      --    (-3+1)x + 4y = -3  ⟹  -2x + 4y = -3
      -- 2. Observe that the second equation is equivalent to the first equation (multiplied by -1)
      -- 3. Therefore, the system simplifies to a single equation 2x - 4y = 3
      -- 4. This equation has infinitely many solutions: for any y, x = (3+4y)/2
      -- 5. Construct an infinite set S and prove it satisfies the requirements

      -- First substitute m = -3 and simplify the system
      have h_system_simplified : ∀ x y : ℝ, system (-3) x y ↔ 2 * x - 4 * y = 3 := by
        intro x y
        unfold system
        ring_nf
        constructor
        · intro h
          exact h.1
        · intro h
          constructor
          · exact h
          . have : -(x * 2) + y * 4 =  - (x * 2 - y * 4) := by
              ring
            rw [this, h]

      -- Construct the solution set
      let S : Set (ℝ × ℝ) := {(x, y) | 2 * x - 4 * y = 3}

      -- Prove that S is the solution set of the system when m = -3
      have h_S_iff : ∀ x y : ℝ, (x, y) ∈ S ↔ system (-3) x y := by
        intro x y
        unfold S
        simp only [Set.mem_setOf_eq]
        exact Iff.symm (h_system_simplified x y)

      -- Prove that the solution set is infinite
      have h_S_infinite : Set.Infinite S := by
        -- Construct a function from R to S
        let f : ℝ → ℝ × ℝ := fun y => ((3 + 4*y)/2, y)

        -- Prove that f indeed maps R to S
        have h_f_range : ∀ y : ℝ, f y ∈ S := by
          intro y
          unfold S
          simp only [Set.mem_setOf_eq]
          -- Calculate if f y satisfies the equation 2x - 4y = 3
          calc
            2 * ((3 + 4*y)/2) - 4 * y = (3 + 4*y) - 4 * y := by ring
            _ = 3 := by ring

        -- Prove that f is injective, i.e., different y map to different points
        have h_f_inj : Function.Injective f := by
          intro y₁ y₂ h
          -- If f y₁ = f y₂, then y₁ = y₂
          unfold f at h
          simp at h
          exact h.2

        -- Use the fact that R is an infinite set and f is injective to derive that S is also an infinite set
        exact Set.infinite_of_injective_forall_mem h_f_inj h_f_range

      -- Construct the final proof
      use S
      constructor
      · exact h_S_infinite
      · intro x y
        rw [h_m_eq_neg3]
        ring_nf
        unfold S
        simp only [Set.mem_setOf_eq]
        ring_nf
        constructor
        · intro h
          constructor
          · exact h
          . have : -(x * 2) + y * 4 =  - (x * 2 - y * 4) := by
              ring
            rw [this, h]
        . intro h
          exact h.1

  -- Second theorem: the system has no solutions if and only if m = 3
  · intro m
    constructor

    -- Direction 1: If the system has no solutions, then m = 3
    · intro h_no_sols
      -- Here we prove: from hasNoSolutions m we derive m = 3

      by_contra h_m_neq_3
      have : m-3 ≠ 0 := by  exact sub_ne_zero.mpr h_m_neq_3
      push_neg at h_no_sols
      have := h_no_sols ((-3)/(m-3)) (3/(m-3))
      field_simp at this
      ring_nf at this
      contradiction

    -- Direction 2: If m = 3, then the system has no solutions
    · intro h_m_eq_3
      -- Assume that a solution exists
      intro h_contra
      -- Deconstruct the assumption
      rcases h_contra with ⟨x, y, h_system⟩

      -- Substitute m = 3 to simplify the equation
      have h_eq : x * 2 + y * 2 = 3 ∧ x * 4 + y * 4 = -3 := by
        rw [h_m_eq_3] at h_system
        ring_nf at h_system
        ring_nf
        exact h_system

      -- Multiply the first equation by 2
      have h_eq1_doubled : 4 * x + 4 * y = 6 := by
        have h_eq1 := h_eq.1
        calc
          4 * x + 4 * y = 2 * (x * 2 + y * 2) := by ring
          _ = 2 * 3 := by rw [h_eq1]
          _ = 6 := by ring

      -- Obtain a contradiction
      linarith
