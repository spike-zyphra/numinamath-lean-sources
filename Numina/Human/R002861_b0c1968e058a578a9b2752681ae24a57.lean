import Mathlib

/--
Problem statement (Main theorem of this file):
2. In a Cartesian coordinate system, a point whose both vertical and horizontal coordinates are integers is called an integer point. Therefore, the number of integer points $(x, y)$ that satisfy the inequality $(|x|-1)^{2}$ $+(|y|-1)^{2}<2$ is
(A) 16
(B) 17
(C) 18
(D) 25

Solution:
(A) 2. [Analysis and Solution] From $(|x|-1)^{2}+(|y|-1)^{2}&lt;2$, we know that $(|x|-1,|y|-1)$ is one of the following: $(0,0),(0$, $1),(0,-1),(1,0)$ or $(-1,0)$. Therefore, the total number of possible values for $(x, y)$ is 16.
-/

theorem inequalities_123191 : Set.encard {p : ℤ × ℤ | (abs p.1 - 1)^2 + (abs p.2 - 1)^2 < 2} = 16 := by
  -- Let S be the set of points satisfying the condition
  let S := {p : ℤ × ℤ | (abs p.1 - 1)^2 + (abs p.2 - 1)^2 < 2}

  -- Analysis: When (|x|-1)^2 + (|y|-1)^2 < 2, the possible values for (|x|-1, |y|-1)
  -- Since (|x|-1)^2 ≥ 0 and (|y|-1)^2 ≥ 0, and their sum is less than 2
  -- We can deduce that (|x|-1, |y|-1) can only be one of the following 5 points:
  -- (0,0), (0,1), (0,-1), (1,0), (-1,0)

  -- The corresponding integer points (x,y) are:
  -- 1. (|x|-1,|y|-1)=(0,0) implies |x|=1, |y|=1, corresponding to: (1,1), (1,-1), (-1,1), (-1,-1) (4 points)
  -- 2. (|x|-1,|y|-1)=(0,1) implies |x|=1, |y|=2, corresponding to: (1,2), (1,-2), (-1,2), (-1,-2) (4 points)
  -- 3. (|x|-1,|y|-1)=(0,-1) implies |x|=1, |y|=0, corresponding to: (1,0), (-1,0) (2 points)
  -- 4. (|x|-1,|y|-1)=(1,0) implies |x|=2, |y|=1, corresponding to: (2,1), (2,-1), (-2,1), (-2,-1) (4 points)
  -- 5. (|x|-1,|y|-1)=(-1,0) implies |x|=0, |y|=1, corresponding to: (0,1), (0,-1) (2 points)
  -- Total: 4+4+2+4+2 = 16 points

  -- Proof steps:

  -- First, we prove that if (a,b) satisfies a^2+b^2<2, then (a,b) must be one of the 5 points mentioned above
  have h_ab_lt_2 : ∀ a b : ℤ, a^2 + b^2 < 2 →
    (a = 0 ∧ b = 0) ∨
    (a = 0 ∧ b = 1) ∨
    (a = 0 ∧ b = -1) ∨
    (a = 1 ∧ b = 0) ∨
    (a = -1 ∧ b = 0) := by

    intro a b h
    -- Here we need to prove that if a^2+b^2<2, then (a,b) must be one of the 5 points
    by_cases h_a_eq_0 : a = 0
    . have : b = 0 ∨ b = 1 ∨ b = -1 := by
        rw [h_a_eq_0] at h
        simp at h
        have : b^2 ≤ 1 := by omega
        by_cases h_b_sq_1 : b^2 = 1
        . simp at h_b_sq_1
          right
          exact h_b_sq_1
        . push_neg at h_b_sq_1
          have : b^2 ≤ 0 := by omega
          have : b^2 ≥ 0 := by positivity
          have : b^2 = 0 := by linarith
          simp at this
          left
          exact this

      cases' this with hb0 hb1
      . left
        exact ⟨ h_a_eq_0, hb0 ⟩
      . cases' hb1 with hb1_1 hb1_2
        . right;left
          exact ⟨ h_a_eq_0, hb1_1 ⟩
        . right;right;left
          exact ⟨ h_a_eq_0, hb1_2 ⟩

    . by_cases h_a_sq_1 : a^2 = 1
      . have : b = 0 := by
          rw [h_a_sq_1] at h
          have : b^2 < 1 := by linarith
          have : b^2 ≤ 0 := by omega
          have : b^2 ≥ 0 := by positivity
          have : b^2 = 0 := by linarith
          simp at this
          exact this

        have : a = 1 ∨ a = -1 := by
          simp at h_a_sq_1
          exact h_a_sq_1
        cases' this with ha1 ha_n1
        . right;right;right;left
          exact ⟨ ha1, this ⟩
        . right;right;right;right
          exact ⟨ ha_n1, this ⟩
      . have a_ge_2 : a^2 ≥ 2 := by
          by_contra h_contra
          simp at h_contra
          push_neg at h_a_eq_0
          push_neg at h_a_sq_1
          have : a^2 < 1 := by omega
          have : a^2 ≤ 0 := by omega
          have : a^2 ≥ 0 := by positivity
          have : a^2 = 0 := by linarith
          simp at this
          contradiction
        have : b^2 ≥ 0 := by positivity
        have : a^2 + b^2 ≥ 2 := by linarith
        linarith

  -- Next, we define set T containing the 16 points analyzed above
  let T : Finset (ℤ × ℤ) := {
    (1,1), (1,-1), (-1,1), (-1,-1),    -- |x|=1, |y|=1
    (1,2), (1,-2), (-1,2), (-1,-2),    -- |x|=1, |y|=2
    (1,0), (-1,0),                    -- |x|=1, |y|=0
    (2,1), (2,-1), (-2,1), (-2,-1),    -- |x|=2, |y|=1
    (0,1), (0,-1)                     -- |x|=0, |y|=1
  }


  -- Then we prove S=T, meaning S and T contain the same points
  have h_S_eq_T : S = T := by
    -- Prove both directions: S ⊆ T and T ⊆ S
    ext p  -- Use extension principle to prove for any point p, p ∈ S ↔ p ∈ T

    -- Bidirectional proof
    constructor

    -- Direction 1: S ⊆ T, meaning if p∈S, then p∈T
    · intro h_p_in_S

      -- If p∈S, then p satisfies the inequality (|p.1|-1)^2 + (|p.2|-1)^2 < 2
      -- We need to prove p is also in T, meaning p is one of the 16 points we listed

      -- Let a = |p.1|-1, b = |p.2|-1, then a^2 + b^2 < 2
      let a := abs p.1 - 1
      let b := abs p.2 - 1

      -- Apply h_ab_lt_2 lemma to show (a,b) is one of the 5 points
      have h_ab_cases := h_ab_lt_2 a b h_p_in_S

      -- Case analysis
      rcases h_ab_cases with (⟨ha0, hb0⟩ | ⟨ha0, hb1⟩ | ⟨ha0, hbn1⟩ | ⟨ha1, hb0⟩ | ⟨han1, hb0⟩)
      . -- Case 1: (a,b)=(0,0)
        have h1 : p.1 = 1 ∨ p.1 = -1 := by
          unfold a at ha0
          rw [sub_eq_zero, abs_eq] at ha0
          exact ha0
          linarith

        have h2 : p.2 = 1 ∨ p.2 = -1 := by
          unfold b at hb0
          rw [sub_eq_zero, abs_eq] at hb0
          exact hb0
          linarith

        cases' h1 with h1_1 h1_2
        . cases' h2 with h2_1 h2_2
          . have : p = (1, 1) := by
              ext
              simp
              exact h1_1
              exact h2_1
            rw [this]
            unfold T
            decide
          . have : p = (1, -1) := by
              ext
              simp
              exact h1_1
              exact h2_2
            rw [this]
            unfold T
            decide
        . cases' h2 with h2_1 h2_2
          . have : p = (-1, 1) := by
              ext
              simp
              exact h1_2
              exact h2_1
            rw [this]
            unfold T
            decide
          . have : p = (-1, -1) := by
              ext
              simp
              exact h1_2
              exact h2_2
            rw [this]
            unfold T
            decide
      . -- Case 2: (a,b)=(0,1)
        -- From a = |p.1| - 1 = 0, we get |p.1| = 1
        have h1 : |p.1| = 1 := by
          unfold a at ha0
          rw [sub_eq_zero] at ha0
          exact ha0

        -- From b = |p.2| - 1 = 1, we get |p.2| = 2
        have h2 : |p.2| = 2 := by
          unfold b at hb1
          have : |p.2| - 1 = 1 := hb1
          linarith

        -- When |p.1| = 1, p.1 could be 1 or -1
        have h3 : p.1 = 1 ∨ p.1 = -1 := by
          cases' eq_or_eq_neg_of_abs_eq h1 with h_pos h_neg
          · left; exact h_pos
          · right; exact h_neg

        -- When |p.2| = 2, p.2 could be 2 or -2
        have h4 : p.2 = 2 ∨ p.2 = -2 := by
          cases' eq_or_eq_neg_of_abs_eq h2 with h_pos h_neg
          · left; exact h_pos
          · right; exact h_neg

        -- Case analysis
        cases' h3 with h3_1 h3_2
        · cases' h4 with h4_1 h4_2
          · -- p.1 = 1, p.2 = 2
            have : p = (1, 2) := by
              ext
              · exact h3_1
              · exact h4_1
            rw [this]
            unfold T
            decide
          · -- p.1 = 1, p.2 = -2
            have : p = (1, -2) := by
              ext
              · exact h3_1
              · exact h4_2
            rw [this]
            unfold T
            decide
        · cases' h4 with h4_1 h4_2
          · -- p.1 = -1, p.2 = 2
            have : p = (-1, 2) := by
              ext
              · exact h3_2
              · exact h4_1
            rw [this]
            unfold T
            decide
          · -- p.1 = -1, p.2 = -2
            have : p = (-1, -2) := by
              ext
              · exact h3_2
              · exact h4_2
            rw [this]
            unfold T
            decide
      . -- Case 3: (a,b)=(0,-1)
        -- From a = |p.1| - 1 = 0, we get |p.1| = 1
        have h1 : |p.1| = 1 := by
          unfold a at ha0
          rw [sub_eq_zero] at ha0
          exact ha0

        -- From b = |p.2| - 1 = -1, we get |p.2| = 0
        have h2 : |p.2| = 0 := by
          unfold b at hbn1
          have : |p.2| - 1 = -1 := hbn1
          linarith

        -- When |p.1| = 1, p.1 could be 1 or -1
        have h3 : p.1 = 1 ∨ p.1 = -1 := by
          cases' eq_or_eq_neg_of_abs_eq h1 with h_pos h_neg
          · left; exact h_pos
          · right; exact h_neg

        -- When |p.2| = 0, p.2 must be 0
        have h4 : p.2 = 0 := by
          rw [abs_eq_zero] at h2
          exact h2

        -- Case analysis
        cases' h3 with h3_1 h3_2
        · -- p.1 = 1, p.2 = 0
          have : p = (1, 0) := by
            ext
            · exact h3_1
            · exact h4
          rw [this]
          unfold T
          decide
        · -- p.1 = -1, p.2 = 0
          have : p = (-1, 0) := by
            ext
            · exact h3_2
            · exact h4
          rw [this]
          unfold T
          decide
      . -- Case 4: (a,b)=(1,0)
        -- From a = |p.1| - 1 = 1, we get |p.1| = 2
        have h1 : |p.1| = 2 := by
          unfold a at ha1
          have : |p.1| - 1 = 1 := ha1
          linarith

        -- From b = |p.2| - 1 = 0, we get |p.2| = 1
        have h2 : |p.2| = 1 := by
          unfold b at hb0
          rw [sub_eq_zero] at hb0
          exact hb0

        -- When |p.1| = 2, p.1 could be 2 or -2
        have h3 : p.1 = 2 ∨ p.1 = -2 := by
          cases' eq_or_eq_neg_of_abs_eq h1 with h_pos h_neg
          · left; exact h_pos
          · right; exact h_neg

        -- When |p.2| = 1, p.2 could be 1 or -1
        have h4 : p.2 = 1 ∨ p.2 = -1 := by
          cases' eq_or_eq_neg_of_abs_eq h2 with h_pos h_neg
          · left; exact h_pos
          · right; exact h_neg

        -- Case analysis
        cases' h3 with h3_1 h3_2
        · cases' h4 with h4_1 h4_2
          · -- p.1 = 2, p.2 = 1
            have : p = (2, 1) := by
              ext
              · exact h3_1
              · exact h4_1
            rw [this]
            unfold T
            decide
          · -- p.1 = 2, p.2 = -1
            have : p = (2, -1) := by
              ext
              · exact h3_1
              · exact h4_2
            rw [this]
            unfold T
            decide
        · cases' h4 with h4_1 h4_2
          · -- p.1 = -2, p.2 = 1
            have : p = (-2, 1) := by
              ext
              · exact h3_2
              · exact h4_1
            rw [this]
            unfold T
            decide
          · -- p.1 = -2, p.2 = -1
            have : p = (-2, -1) := by
              ext
              · exact h3_2
              · exact h4_2
            rw [this]
            unfold T
            decide
      . -- Case 5: (a,b)=(-1,0)
        have h1 : p.1 = 0 := by
          unfold a at han1
          simp at han1
          exact han1

        have h2 : p.2 = 1 ∨ p.2 = -1:= by
          unfold b at hb0
          rw [sub_eq_zero, abs_eq] at hb0
          exact hb0
          linarith

        cases' h2 with h2_1 h2_2
        . have : p = (0, 1) := by
            ext
            simp
            . exact h1
            . exact h2_1

          rw [this]
          unfold T
          decide
        . have : p = (0, -1) := by
            ext
            simp
            . exact h1
            . exact h2_2

          rw [this]
          unfold T
          decide
    -- Direction 2: T ⊆ S, meaning if p∈T, then p∈S
    · intro h_p_in_T
      -- We need to prove: (|p.1| - 1)^2 + (|p.2| - 1)^2 < 2

      -- Instead of explicitly listing all 16 points, we can prove
      -- that any point in T satisfies the inequality directly
      have : ∀ q ∈ T, (abs q.1 - 1)^2 + (abs q.2 - 1)^2 < 2 := by
        intro q hq
        -- For each point in T, we can verify the condition directly
        simp only [Finset.mem_insert, Finset.mem_singleton, T] at hq

        rcases hq with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
        all_goals decide

      -- Apply the general result to our specific point p
      exact this p h_p_in_T

  -- Finally, we prove the cardinality of T is 16
  have h_card_T : Finset.card T = 16 := by
    -- Calculate the cardinality of T
    -- T contains the following points:
    -- 1. (1,1), (1,-1), (-1,1), (-1,-1) - 4 points
    -- 2. (1,2), (1,-2), (-1,2), (-1,-2) - 4 points
    -- 3. (1,0), (-1,0) - 2 points
    -- 4. (2,1), (2,-1), (-2,1), (-2,-1) - 4 points
    -- 5. (0,1), (0,-1) - 2 points
    -- Total 4+4+2+4+2=16 points
    decide

  -- Since S=T, the cardinality of S is also 16
  calc
    Set.encard S = Finset.card T := by rw [h_S_eq_T]; simp
    _           = 16            := by rw [h_card_T]; simp
