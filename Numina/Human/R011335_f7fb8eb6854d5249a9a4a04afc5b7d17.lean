import Mathlib
open Real

/--
Problem statement:
If the equation $\left|  \left|  2m+5\right|  -b\right|  =5$ has three distinct solutions for $m$, then the rational number $b=$ ___          ___ .

-/
theorem algebra_624155 (b : ℝ) :
    {m : ℝ | abs (abs (2 * m + 5) - b) = 5}.encard = 3 ↔ b = 5:= by

  let S := {m : ℝ | abs (abs (2 * m + 5) - b) = 5}

  -- First, analyze the equation ||(2*m+5)|-b|=5 to obtain an equivalent form
  have h_S1 : S = {m : ℝ | abs (2 * m + 5) = b + 5 ∨ abs (2 * m + 5) = b - 5} := by
    unfold S
    ext m
    simp only [Set.mem_setOf_eq]
    constructor
    . intro h
      rw [abs_eq (by positivity)] at h
      cases' h with h1 h2
      . left
        linarith
      . right
        linarith
    . intro h
      rw [abs_eq (by positivity)]
      cases' h with h1 h2
      . left
        rw [h1]
        simp
      . right
        rw [h2]
        simp

  -- Analyze the number of solutions in different cases

  -- Case 1: When b < -5, there is no solution
  have h_case0 : b < -5 → S.encard = 0 := by
    intro h
    have h_S_empty : S = ∅ := by
      rw [h_S1]
      simp only [Set.ext_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro x
      have h_abs_nonneg : abs (2 * x + 5) ≥ 0 := abs_nonneg (2 * x + 5)
      by_contra h_contra
      cases' h_contra with h_contra1 h_contra2
      . rw [h_contra1] at h_abs_nonneg
        linarith
      . rw [h_contra2] at h_abs_nonneg
        linarith
    rw [h_S_empty]
    simp

  -- Case 2: When b = -5, there is 1 solution
  have h_case1 : b = -5 → S.encard = 1 := by
    intro h
    have h_S_single : S = {m : ℝ | 2 * m + 5 = 0} := by
      rw [h_S1]
      simp only [Set.ext_iff, Set.mem_setOf_eq]
      intro x
      rw [h]
      simp
      ring_nf
      intro h1
      have := abs_nonneg (5 + x * 2)
      rw [h1] at this
      linarith

    have : S = {m : ℝ | m = - 5 / 2} := by
      rw [h_S_single]
      simp only [Set.ext_iff, Set.mem_setOf_eq]
      intro x
      field_simp
      constructor
      . intro h2
        linarith
      . intro h2
        linarith

    rw [this]
    simp [this]

  -- Case 3: When -5 < b < 5, there are 2 solutions
  have h_case2 : -5 < b → b < 5 → S.encard = 2 := by
    intro h1 h2
    have h_S_two : S = {m : ℝ | 2 * m + 5 = b + 5 ∨ 2 * m + 5 = - (b + 5)} := by
      rw [h_S1]
      simp only [Set.ext_iff, Set.mem_setOf_eq]
      intro x
      constructor
      . intro h3
        cases' h3 with h31 h32
        . have : 0 <= b+5 := by linarith
          rw [abs_eq this] at h31
          exact h31
        . have := abs_nonneg (2 * x + 5)
          rw [h32] at this
          linarith
      . intro h3
        have : 0 <= b+5 := by linarith
        rw [<- abs_eq this] at h3
        left; exact h3

    have : S = {m : ℝ | m = b / 2 ∨ m = - (b + 10) / 2} := by
      rw [h_S_two]
      simp only [Set.ext_iff, Set.mem_setOf_eq]
      intro x
      constructor
      . intro h3
        cases' h3 with h31 h32
        . left
          linarith
        . right
          linarith
      . intro h3
        cases' h3 with h31 h32
        . left
          rw [h31]
          field_simp
        . right
          rw [h32]
          field_simp
          ring_nf

    rw [this]
    apply Set.encard_pair
    by_contra h_contra
    linarith

  -- Case 4: When b = 5, there are 3 solutions
  have h_case3 : b = 5 → S.encard = 3 := by
    intro h
    have h_S_three : S = {m : ℝ | |2 * m + 5| = 10 ∨ 2 * m + 5 = 0} := by
      rw [h_S1, h]
      simp only [Set.ext_iff, Set.mem_setOf_eq]
      intro x
      ring_nf
      rw [abs_eq_zero]

    have : S = {m : ℝ | m = 5 / 2 ∨ m = -15 / 2 ∨ m = -5 / 2} := by
      rw [h_S_three]
      simp only [Set.ext_iff, Set.mem_setOf_eq]
      intro x
      constructor
      . intro h1
        cases' h1 with h11 h12
        . rw [abs_eq (by positivity)] at h11
          cases' h11 with h111 h112
          . left
            linarith
          . right; left
            linarith
        . right; right
          linarith
      . intro h1
        cases' h1 with h11 h12
        . rw [h11]
          ring_nf
          simp
        . cases' h12 with h121 h122
          . rw [h121]
            ring_nf
            simp
          . rw [h122]
            ring_nf
            simp

    rw [this]
    rw [Set.encard_eq_three]
    use 5 / 2, -15 / 2, -5 / 2
    constructor
    . linarith
    . constructor
      . linarith
      . constructor
        . linarith
        . apply Set.ext
          intro x
          simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]

  -- Case 5: When b > 5, there are 4 solutions
  have h_case4 : b > 5 → S.encard = 4 := by
    intro h

    let S1 := {m : ℝ | m = b / 2 ∨ m = - (b + 10) / 2}
    let S2 := {m : ℝ | m = (b - 10) / 2 ∨ m = - (b) / 2}

    have h_S1_encard : S1.encard = 2 := by
      apply Set.encard_pair
      by_contra h_contra
      linarith

    have h_S2_encard : S2.encard = 2 := by
      apply Set.encard_pair
      by_contra h_contra
      linarith

    have h_S_four : S = S1 ∪ S2 := by
      rw [h_S1]
      simp only [Set.ext_iff, Set.mem_setOf_eq]
      intro x
      constructor
      . intro h1
        cases' h1 with h11 h12
        . left
          rw [abs_eq (by positivity)] at h11
          cases' h11 with h111 h112
          . have : x = b / 2 := by linarith
            rw [this]
            unfold S1
            simp
          . have : x = - (b + 10) / 2 := by linarith
            rw [this]
            unfold S1
            simp
        . right
          rw [abs_eq (by linarith)] at h12
          cases' h12 with h121 h122
          . left
            linarith
          . right
            linarith

      . intro h1
        cases' h1 with h11 h12
        . left
          unfold S1 at h11
          simp at h11
          cases' h11 with h111 h112
          . rw [h111]
            ring_nf
            simp
            positivity
          . rw [h112]
            ring_nf
            rw [abs_eq (by positivity)]
            right
            linarith
        . right
          unfold S2 at h12
          simp at h12
          cases' h12 with h121 h122
          . rw [h121]
            ring_nf
            simp
            linarith
          . rw [h122]
            ring_nf
            rw [abs_eq (by linarith)]
            right
            linarith

    have h_S_non_intersect : S1 ∩ S2 = ∅ := by
      apply Set.ext
      intro x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      by_contra h_contra
      have h1 := h_contra.1
      have h2 := h_contra.2
      unfold S1 at h1
      simp at h1
      unfold S2 at h2
      simp at h2
      cases' h1 with h11 h12
      . rw [h11] at h2
        cases' h2 with h21 h22
        . have : b = b+5 := by linarith
          linarith
        . have : b = -5 := by linarith
          linarith
      . rw [h12] at h2
        cases' h2 with h21 h22
        . have : b = b-5 := by linarith
          linarith
        . have : b = -5 := by linarith
          linarith

    have h_S_four_encard : S.encard = S1.encard + S2.encard := by
      have := Set.encard_union_add_encard_inter S1 S2
      rw [h_S_non_intersect, ← h_S_four] at this
      simp at this
      exact this

    rw [h_S_four_encard, h_S1_encard, h_S2_encard]
    norm_num

  constructor
  . intro h
    by_cases h_b1 : b < -5
    · have := h_case0 h_b1
      rw [h] at this
      contradiction
    · by_cases h_b2 : b = -5
      . have := h_case1 h_b2
        rw [h] at this
        contradiction
      . by_cases h_b3 : b < 5
        . push_neg at h_b1
          have : -5<b := lt_of_le_of_ne h_b1 (Ne.symm h_b2)
          have := h_case2 this h_b3
          rw [h] at this
          contradiction
        . by_cases h_b4 : b = 5
          . exact h_b4
          . push_neg at h_b3
            have : b > 5 := lt_of_le_of_ne h_b3 (Ne.symm h_b4)
            have := h_case4 this
            rw [h] at this
            contradiction
  . intro h
    have := h_case3 h
    exact this
