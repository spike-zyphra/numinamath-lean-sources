import Mathlib

open Real
/-There exist several solutions to the equation
1 + sinx / sin4x = sin3x / sin2x
where x is expressed in degrees and 0 < x < π.
Find the sum of all such solutions.-/
theorem algebra_610161: ∑ᶠ x ∈ {x: ℝ | 0 < x ∧ x < π ∧ sin (4 * x) ≠ 0 ∧
 1 + sin x / sin (4 * x) = sin (3 * x) / sin (2 * x)}, x = 16 * π / 9 := by

 -- we directly compute all possible x
  have set_eq: {x: ℝ | 0 < x ∧ x < π ∧ sin (4 * x) ≠ 0 ∧
  1 + sin x / sin (4* x) = sin (3 * x) / sin (2 * x)}
 = {π / 9, 3 * π / 9, 5 * π / 9, 7 * π / 9} := by

    -- we first simplify the condition
    have eqiv: ∀ x: ℝ, 0 < x ∧ x < π ∧ sin (4 * x) ≠ 0 →
    (1 + sin x / sin (4 * x) = sin (3 * x) / sin (2 * x) ↔ sin (4 * x) = sin (5 * x)):= by
      intro x hx
      rcases hx with ⟨hx1, hx2, hx3⟩
      constructor
      -- the forward direction
      . intro h
        have id: sin (4 * x) = 2 * sin (2 * x) * cos (2 * x) := by
          rw [show 4 * x = 2 * (2 * x) by ring]; rw [Real.sin_two_mul]
        rw [id] at h
        have hx4: sin (2 * x) ≠ 0 := by
          by_contra! o
          have l: sin (4 * x) = 0 := by
            rw [id]
            simp [o]
          tauto
        have hx5: cos (2 * x) ≠ 0 := by
          by_contra! o
          have l: sin (4 * x) = 0 := by
            rw [id]
            simp [o]
          tauto
        field_simp at h
        replace h: sin (2 * x) * (2 * sin (2 * x) * cos (2 * x) + sin x - 2 * sin (3 * x) * cos (2 * x)) = 0 := by nlinarith
        simp [hx4] at h
        rw [← id] at h
        have id2: 2 * sin (3 * x) * cos (2 * x) = sin (5 * x) + sin x := by  --show the second identity
          rw [show 5 * x = 3 * x + 2 * x by ring]
          rw [Real.sin_add]
          rw [show x = 3 * x - 2 * x by ring]
          rw [Real.sin_sub]
          ring_nf
        rw [id2] at h
        nlinarith [h]
      -- the backward direction
      . intro h
        have id: sin (4 * x) = 2 * sin (2 * x) * cos (2 * x) := by
          rw [show 4 * x = 2 * (2 * x) by ring]; rw [Real.sin_two_mul]
        rw [id]
        have hx4: sin (2 * x) ≠ 0 := by
          by_contra! o
          have l: sin (4 * x) = 0 := by
            rw [id]
            simp [o]
          tauto
        have hx5: cos (2 * x) ≠ 0 := by
          by_contra! o
          have l: sin (4 * x) = 0 := by
            rw [id]
            simp [o]
          tauto
        field_simp
        have id2: 2 * sin (3 * x) * cos (2 * x) = sin (5 * x) + sin x := by  --show the second identity
          rw [show 5 * x = 3 * x + 2 * x by ring]
          rw [Real.sin_add]
          rw [show x = 3 * x - 2 * x by ring]
          rw [Real.sin_sub]
          ring_nf
        rw [show sin (3 * x) * (2 * sin (2 * x) * cos (2 * x)) = 2 * sin (3 * x) * cos (2 * x) * sin (2 * x) by ring]
        rw [id2]
        rw [← h]
        rw [id]

    -- then we can show the set_eq
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    . intro h
      rcases h with ⟨hx1, hx2, hx3, h⟩
      specialize eqiv x ⟨hx1, hx2, hx3⟩
      rw [eqiv] at h
      clear eqiv
      rw [Real.sin_eq_sin_iff] at h
      obtain ⟨k, h⟩ := h
      rcases h with h | h
      . replace h: x = 2 * ↑k * π := by linarith
        have o1: 0 < (k: ℝ) := by
          nlinarith [Real.pi_gt_d2]
        have o2: (k: ℝ) < 1 := by
          nlinarith [Real.pi_gt_d2]
        simp at o1 o2
        norm_cast at o2
        omega
      . replace h: x = (2 * ↑k + 1) * π / 9 := by nlinarith
        have o1: -1 < (k: ℝ) := by
          nlinarith [Real.pi_gt_d2]
        have o2: (k: ℝ) < 4 := by
          nlinarith [Real.pi_gt_d2]
        norm_cast at o1 o2
        simp at o1
        interval_cases k
        all_goals simp [h]
        . right
          left
          ring
        . right
          right
          left
          ring
        . right
          right
          right
          ring
    . intro h
      simp at h
      specialize eqiv x
      have o: 0 < x ∧ x < π ∧ sin (4 * x) ≠ 0 := by
        rcases h with h | h | h | h
        all_goals simp [h]
        . constructor
          . nlinarith [Real.pi_gt_d2]
          . constructor
            . nlinarith [Real.pi_gt_d2]
            . by_contra! no
              rw [Real.sin_eq_zero_iff] at no
              obtain ⟨k, no⟩ := no
              replace no: k = (4: ℝ) / 9 := by nlinarith [Real.pi_gt_d2]
              have o1: 0 < (k: ℝ) := by linarith
              have o2: (k: ℝ) < 1 := by linarith
              norm_cast at o1 o2
              omega
        . constructor
          . nlinarith [Real.pi_gt_d2]
          . constructor
            . nlinarith [Real.pi_gt_d2]
            . by_contra! no
              rw [Real.sin_eq_zero_iff] at no
              obtain ⟨k, no⟩ := no
              replace no: k = (12: ℝ) / 9 := by nlinarith [Real.pi_gt_d2]
              have o1: 1 < (k: ℝ) := by linarith
              have o2: (k: ℝ) < 2 := by linarith
              norm_cast at o1 o2
              omega
        . constructor
          . nlinarith [Real.pi_gt_d2]
          . constructor
            . nlinarith [Real.pi_gt_d2]
            . by_contra! no
              rw [Real.sin_eq_zero_iff] at no
              obtain ⟨k, no⟩ := no
              replace no: k = (20: ℝ) / 9 := by nlinarith [Real.pi_gt_d2]
              have o1: 2 < (k: ℝ) := by linarith
              have o2: (k: ℝ) < 3 := by linarith
              norm_cast at o1 o2
              omega
        . constructor
          . nlinarith [Real.pi_gt_d2]
          . constructor
            . nlinarith [Real.pi_gt_d2]
            . by_contra! no
              rw [Real.sin_eq_zero_iff] at no
              obtain ⟨k, no⟩ := no
              replace no: k = (28: ℝ) / 9 := by nlinarith [Real.pi_gt_d2]
              have o1: 3 < (k: ℝ) := by linarith
              have o2: (k: ℝ) < 4 := by linarith
              norm_cast at o1 o2
              omega

      simp [o] at eqiv
      rw [eqiv]
      rcases h with h | h | h | h
      . simp [h] at *
        simp [o]
        clear *-
        rw [Real.sin_eq_sin_iff]
        use 0
        right
        simp
        ring
      . simp [h] at *
        simp [o]
        clear *-
        rw [Real.sin_eq_sin_iff]
        use 1
        right
        ring
      . simp [h] at *
        simp [o]
        clear *-
        rw [Real.sin_eq_sin_iff]
        use 2
        right
        ring
      . simp [h] at *
        simp [o]
        clear *-
        rw [Real.sin_eq_sin_iff]
        use 3
        right
        ring


 -- then we compute the sum of elements in the derived set step by step
  rw [set_eq]
  rw [finsum_mem_eq_finite_toFinset_sum]
  simp
  have o1: ∑ x ∈ {π / 9, 3 * π / 9, 5 * π / 9, 7 * π / 9}, x
  = π / 9 + ∑ x ∈ {3 * π / 9, 5 * π / 9, 7 * π / 9}, x := by
     rw [Finset.sum_insert]
     simp
     constructor
     . nlinarith [Real.pi_gt_d2]
     . constructor
       . nlinarith [Real.pi_gt_d2]
       . nlinarith [Real.pi_gt_d2]
  rw [o1]
  clear o1
  have o2: ∑ x ∈ {3 * π / 9, 5 * π / 9, 7 * π / 9}, x
  = 3 * π / 9 + ∑ x ∈ {5 * π / 9, 7 * π / 9}, x := by
     rw [Finset.sum_insert]
     simp
     constructor
     . nlinarith [Real.pi_gt_d2]
     . nlinarith [Real.pi_gt_d2]
  rw [o2]
  clear o2
  have o3: ∑ x ∈ {5 * π / 9, 7 * π / 9}, x
  = 5 * π / 9 + ∑ x ∈ {7 * π / 9}, x := by
     rw [Finset.sum_insert]
     simp
     nlinarith [Real.pi_gt_d2]
  rw [o3]
  clear o3
  have o4: ∑ x ∈ {7 * π / 9}, x
  = 7 * π / 9 := by
     rw [Finset.sum_singleton]
  rw [o4]
  clear o4
  ring
  simp [Set.Finite]
  rw [Set.finite_coe_iff]
  apply Set.toFinite
  