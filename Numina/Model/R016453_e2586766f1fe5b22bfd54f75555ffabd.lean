import Mathlib

theorem algebra_225614 (S : Set ℝ) (hS : S = {x | abs (x - abs (2 * x + 1)) = 3}) :
    S.encard = 2 := by
  have h1 : S = {2, -4 / 3} := by
    ext x
    simp [hS]
    constructor
    · -- Assume abs (x - abs (2 * x + 1)) = 3, prove x ∈ {2, -4 / 3}
      intro h
      by_cases h2 : 2 * x + 1 ≥ 0
      · -- If 2 * x + 1 ≥ 0, then |2x + 1| = 2x + 1
        have h3 : abs (2 * x + 1) = 2 * x + 1 := by
          rw [abs_of_nonneg h2]
        have h4 : abs (x - abs (2 * x + 1)) = abs (x - (2 * x + 1)) := by
          rw [h3]
        rw [h4] at h
        have h5 : abs (x - (2 * x + 1)) = abs (- (x + 1)) := by
          ring_nf
        rw [h5] at h
        have h6 : abs (- (x + 1)) = abs (x + 1) := by
          rw [abs_neg]
        rw [h6] at h
        cases' eq_or_eq_neg_of_abs_eq h with h7 h8
        · -- Case x + 1 = 3
          have hx2 : x = 2 := by linarith
          left
          linarith
        · -- Case x + 1 = -3
          have hx4 : x = -4 := by linarith
          exfalso
          linarith [h2, hx4]
      · -- If 2 * x + 1 < 0
        have h4 : abs (2 * x + 1) = - (2 * x + 1) := by
          rw [abs_of_neg (lt_of_not_ge h2)]
        have h5 : abs (x - abs (2 * x + 1)) = abs (x - (- (2 * x + 1))) := by
          rw [h4]
        rw [h5] at h
        have h6 : x - (- (2 * x + 1)) = 3 * x + 1 := by linarith
        rw [h6] at h
        cases' eq_or_eq_neg_of_abs_eq h with h7 h8
        · -- Case 3 * x + 1 = 3
          have hx2_3 : x = 2 / 3 := by linarith
          exfalso
          linarith [h2, hx2_3]
        · -- Case 3 * x + 1 = -3
          have hx4_3 : x = -4 / 3 := by linarith
          right
          linarith
    · -- Assume x ∈ {2, -4/3}, prove abs (x - abs (2 * x + 1)) = 3
      rintro (h | h)
      · -- Case x = 2
        rw [h]
        norm_num [abs]
      · -- Case x = -4/3
        rw [h]
        norm_num [abs]
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_pair]
  all_goals norm_num