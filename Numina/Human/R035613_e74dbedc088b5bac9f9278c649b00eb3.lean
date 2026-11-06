import Mathlib

/- $1 \cdot 11$ If $a b c>0$, then $\frac{|a|}{a}+\frac{|b|}{b}+\frac{|c|}{c}-\frac{a b c}{|a b c|}$ is
(A) 2.
(B) -2.
(C) 2 or -2.
(D) None of the above.
(China Hubei Province Huanggang Junior High School Mathematics Competition, 1993) -/
theorem algebra_143066 {a b c : ℝ} (habc : a * b * c > 0) :
    (|a| / a + |b| / b + |c| / c - a * b * c / |a * b * c|) = 2 ∨
    (|a| / a + |b| / b + |c| / c - a * b * c / |a * b * c|) = -2 := by
  -- Prove that a is non-zero (since a*b*c > 0)
  have h1 : a ≠ 0 := by
    by_contra h
    rw [h] at habc
    simp at habc
  -- Prove that b is non-zero (since a*b*c > 0)
  have h2 : b ≠ 0 := by
    by_contra h
    rw [h] at habc
    simp at habc
  -- Prove that c is non-zero (since a*b*c > 0)
  have h3 : c ≠ 0 := by
    by_contra h
    rw [h] at habc
    simp at habc
  -- Simplify the last term: a*b*c/|a*b*c| = 1 since a*b*c > 0
  have h4 : a * b * c / |a * b * c| = 1 := by
    have h_pos : |a * b * c| = a * b * c := by
      rw [abs_of_pos habc]
    field_simp [h_pos]
  -- Case analysis on whether a is positive
  by_cases ha_pos : a > 0
  · -- If a > 0
    -- When a > 0, |a|/a = 1
    have ha : |a| / a = 1 := by
      rw [abs_of_pos ha_pos]
      field_simp [h1]
    -- Case analysis on whether b is positive
    by_cases hb_pos : b > 0
    · -- If b > 0
      -- When b > 0, |b|/b = 1
      have hb : |b| / b = 1 := by
        rw [abs_of_pos hb_pos]
        field_simp [h2]
      -- If a > 0 and b > 0, then c must be positive for a*b*c > 0
      have hc_pos : c > 0 := by
        by_contra h
        push_neg at h
        have h4 : a * b > 0 := mul_pos ha_pos hb_pos
        have h5 : a * b * c ≤ 0 := by nlinarith [h4, h]
        linarith
      -- When c > 0, |c|/c = 1
      have hc : |c| / c = 1 := by
        rw [abs_of_pos hc_pos]
        field_simp [h3]
      -- Calculate the final expression when a,b,c > 0
      have h : |a| / a + |b| / b + |c| / c - a * b * c / |a * b * c| = 2 := by
        rw [ha, hb, hc, h4]
        norm_num
      left
      exact h
    · -- If b ≤ 0
      -- Since b ≠ 0 and b ≤ 0, we have b < 0
      have hb_neg : b < 0 := by
        by_contra h
        push_neg at h
        have : b = 0 := by linarith
        contradiction
      -- If a > 0 and b < 0, then c must be negative for a*b*c > 0
      have hc_neg : c < 0 := by
        by_contra h
        push_neg at h
        have h4 : a * b < 0 := mul_neg_of_pos_of_neg ha_pos hb_neg
        nlinarith [sq_nonneg (a * b), sq_nonneg c]
      -- When b < 0, |b|/b = -1
      have hb : |b| / b = -1 := by
        rw [abs_of_neg hb_neg]
        field_simp [h2]
      -- When c < 0, |c|/c = -1
      have hc : |c| / c = -1 := by
        rw [abs_of_neg hc_neg]
        field_simp [h3]
      -- Calculate the final expression when a > 0, b < 0, c < 0
      have h : |a| / a + |b| / b + |c| / c - a * b * c / |a * b * c| = -2 := by
        rw [ha, hb, hc, h4]
        norm_num
      right
      exact h
  · -- If a ≤ 0
    -- Since a ≠ 0 and a ≤ 0, we have a < 0
    have ha_neg : a < 0 := by
      by_contra h
      push_neg at h
      have : a = 0 := by linarith
      contradiction
    -- When a < 0, |a|/a = -1
    have ha : |a| / a = -1 := by
      rw [abs_of_neg ha_neg]
      field_simp [h1]
    -- Case analysis on whether b is positive
    by_cases hb_pos : b > 0
    · -- If b > 0
      -- When b > 0, |b|/b = 1
      have hb : |b| / b = 1 := by
        rw [abs_of_pos hb_pos]
        field_simp [h2]
      -- If a < 0 and b > 0, then c must be negative for a*b*c > 0
      have hc_neg : c < 0 := by
        by_contra h
        push_neg at h
        have h4 : a * b < 0 := mul_neg_of_neg_of_pos ha_neg hb_pos
        nlinarith [sq_nonneg (a * b), sq_nonneg c]
      -- When c < 0, |c|/c = -1
      have hc : |c| / c = -1 := by
        rw [abs_of_neg hc_neg]
        field_simp [h3]
      -- Calculate the final expression when a < 0, b > 0, c < 0
      have h : |a| / a + |b| / b + |c| / c - a * b * c / |a * b * c| = -2 := by
        rw [ha, hb, hc, h4]
        norm_num
      right
      exact h
    · -- If b ≤ 0
      -- Since b ≠ 0 and b ≤ 0, we have b < 0
      have hb_neg : b < 0 := by
        by_contra h
        push_neg at h
        have : b = 0 := by linarith
        contradiction
      -- If a < 0 and b < 0, then c must be positive for a*b*c > 0
      have hc_pos : c > 0 := by
        by_contra h
        push_neg at h
        have h4 : a * b > 0 := mul_pos_of_neg_of_neg ha_neg hb_neg
        have h5 : a * b * c ≤ 0 := by nlinarith [h4, h]
        linarith
      -- When b < 0, |b|/b = -1
      have hb : |b| / b = -1 := by
        rw [abs_of_neg hb_neg]
        field_simp [h2]
      -- When c > 0, |c|/c = 1
      have hc : |c| / c = 1 := by
        rw [abs_of_pos hc_pos]
        field_simp [h3]
      -- Calculate the final expression when a < 0, b < 0, c > 0
      have h : |a| / a + |b| / b + |c| / c - a * b * c / |a * b * c| = -2 := by
        rw [ha, hb, hc, h4]
        norm_num
      right
      exact h
