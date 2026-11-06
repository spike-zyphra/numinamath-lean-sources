import Mathlib


open Real


theorem algebra_2713
    {a b c : ℝ} (h₀ : a * b * c > 0) (h₁ : a + b + c = 0) :
    (b + c) / |a| + (c + a) / |b| + (a + b) / |c| = 1 := by

  have ha : a ≠ 0 := by
    by_contra h
    have h2 : a * b * c = 0 := by
      rw [h]
      norm_num
    linarith

  have hb : b ≠ 0 := by
    by_contra h
    have h2 : a * b * c = 0 := by
      rw [h]
      norm_num
    linarith

  have hc : c ≠ 0 := by
    by_contra h
    have h2 : a * b * c = 0 := by
      rw [h]
      norm_num
    linarith

  have e1 : (b + c) / |a| + (c + a) / |b| + (a + b) / |c| = - (a / |a| + b / |b| + c / |c|) := by
    have e2 : b + c = -a := by linarith
    have e3 : c + a = -b := by linarith
    have e4 : a + b = -c := by linarith
    rw [e2, e3, e4]
    ring

  have e5 : a / |a| + b / |b| + c / |c| = -1 := by
    by_cases ha2 : 0 < a
    · -- a > 0
      have ha3 : a > 0 := ha2
      have hb2 : b * c > 0 := by
        nlinarith
      have hb3 : b < 0 := by
        by_contra h
        push_neg at h
        have hb4 : b ≥ 0 := by linarith
        have hc4 : c ≥ 0 := by nlinarith [sq_nonneg (b - c), sq_nonneg (b), sq_nonneg (c), show b * c ≥ 0 by nlinarith]
        nlinarith
      have hc2 : c < 0 := by
        by_contra h
        push_neg at h
        have hc4 : c ≥ 0 := by linarith
        have hb4 : b ≥ 0 := by nlinarith [sq_nonneg (b - c), sq_nonneg (b), sq_nonneg (c), show b * c ≥ 0 by nlinarith]
        nlinarith
      have ha4 : a / |a| = 1 := by
        rw [abs_of_pos ha3]
        field_simp [ha]
      have hb4 : b / |b| = -1 := by
        rw [abs_of_neg (show b < 0 by linarith)]
        field_simp [hb]
      have hc4 : c / |c| = -1 := by
        rw [abs_of_neg (show c < 0 by linarith)]
        field_simp [hc]
      linarith [ha4, hb4, hc4]

    · -- a ≤ 0, so a < 0
      have ha3 : a < 0 := by
        by_contra h
        push_neg at h
        have : a = 0 := by linarith
        tauto
      have hb1 : b * c < 0 := by
        nlinarith
      by_cases hb2 : 0 < b
      · -- b > 0
        have hb3 : b > 0 := hb2
        have hc2 : c < 0 := by
          nlinarith
        have ha4 : a / |a| = -1 := by
          rw [abs_of_neg (show a < 0 by linarith)]
          field_simp [ha]
        have hb4 : b / |b| = 1 := by
          rw [abs_of_pos (show b > 0 by linarith)]
          field_simp [hb]
        have hc4 : c / |c| = -1 := by
          rw [abs_of_neg (show c < 0 by linarith)]
          field_simp [hc]
        linarith [ha4, hb4, hc4]

      · -- b ≤ 0, so b < 0
        have hb3 : b < 0 := by
          by_contra h
          push_neg at h
          have : b = 0 := by linarith
          tauto
        have hc2 : c > 0 := by
          nlinarith
        have ha4 : a / |a| = -1 := by
          rw [abs_of_neg (show a < 0 by linarith)]
          field_simp [ha]
        have hb4 : b / |b| = -1 := by
          rw [abs_of_neg (show b < 0 by linarith)]
          field_simp [hb]
        have hc4 : c / |c| = 1 := by
          rw [abs_of_pos (show c > 0 by linarith)]
          field_simp [hc]
        linarith [ha4, hb4, hc4]

  rw [e1, e5]
  all_goals norm_num