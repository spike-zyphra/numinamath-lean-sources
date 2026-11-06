import Mathlib

/- Rational numbers $a$, $b$, $c$, $d$ satisfy $\frac{\left| abcd \right|}{abcd}=-1$, then the maximum value of $\frac{\left| a \right|}{a}+\frac{\left| b \right|}{b}+\frac{\left| c \right|}{c}+\frac{\left| d \right|}{d}$ is ___          ___. -/
theorem number_theory_1503 :
    IsGreatest {x | ∃ a b c d : ℚ, x = |a| / a + |b| / b + |c| / c + |d| / d ∧ |a * b * c * d| / (a * b * c * d) = -1} 2 := by
  constructor
  · -- Show that 2 is in the set
    use -1, (1 : ℚ), (1 : ℚ), (1 : ℚ)
    norm_num [abs_of_neg, abs_of_pos]
    <;> native_decide
  · -- Show that 2 is the greatest element in the set
    intro x hx
    rcases hx with ⟨a, b, c, d, hx_eq, h_eq⟩

    have ha1 : a ≠ 0 := by
      by_contra h
      rw [h] at h_eq
      norm_num at h_eq
      all_goals try { contradiction }
    have hb1 : b ≠ 0 := by
      by_contra h
      rw [h] at h_eq
      norm_num at h_eq
      all_goals try { contradiction }
    have hc1 : c ≠ 0 := by
      by_contra h
      rw [h] at h_eq
      norm_num at h_eq
      all_goals try { contradiction }
    have hd1 : d ≠ 0 := by
      by_contra h
      rw [h] at h_eq
      norm_num at h_eq
      all_goals try { contradiction }

    have h2 : |a| / a = 1 ∨ |a| / a = -1 := by
      cases (le_or_lt 0 a) with
      | inl h_nonneg =>
        have h4 : |a| = a := by
          rw [abs_of_nonneg h_nonneg]
        have h5 : |a| / a = 1 := by
          field_simp [ha1, h4]
        simp [h5]
      | inr h_pos =>
        have h4 : |a| = -a := by
          rw [abs_of_neg h_pos]
        have h5 : |a| / a = -1 := by
          field_simp [ha1, h4]
        simp [h5]
    have h2b : |b| / b = 1 ∨ |b| / b = -1 := by
      cases (le_or_lt 0 b) with
      | inl h_nonneg =>
        have h4 : |b| = b := by
          rw [abs_of_nonneg h_nonneg]
        have h5 : |b| / b = 1 := by
          field_simp [hb1, h4]
        simp [h5]
      | inr h_pos =>
        have h4 : |b| = -b := by
          rw [abs_of_neg h_pos]
        have h5 : |b| / b = -1 := by
          field_simp [hb1, h4]
        simp [h5]
    have h2c : |c| / c = 1 ∨ |c| / c = -1 := by
      cases (le_or_lt 0 c) with
      | inl h_nonneg =>
        have h4 : |c| = c := by
          rw [abs_of_nonneg h_nonneg]
        have h5 : |c| / c = 1 := by
          field_simp [hc1, h4]
        simp [h5]
      | inr h_pos =>
        have h4 : |c| = -c := by
          rw [abs_of_neg h_pos]
        have h5 : |c| / c = -1 := by
          field_simp [hc1, h4]
        simp [h5]
    have h2d : |d| / d = 1 ∨ |d| / d = -1 := by
      cases (le_or_lt 0 d) with
      | inl h_nonneg =>
        have h4 : |d| = d := by
          rw [abs_of_nonneg h_nonneg]
        have h5 : |d| / d = 1 := by
          field_simp [hd1, h4]
        simp [h5]
      | inr h_pos =>
        have h4 : |d| = -d := by
          rw [abs_of_neg h_pos]
        have h5 : |d| / d = -1 := by
          field_simp [hd1, h4]
        simp [h5]
    -- From h_eq, we have that the product a * b * c * d is negative
    -- We can derive that the product of the signs must be -1
    have h3 : |a * b * c * d| = |a| * |b| * |c| * |d| := by
      simp [abs_mul, abs_mul]
    have h4 : |a| * |b| * |c| * |d| / (a * b * c * d) = -1 := by
      rw [show |a * b * c * d| = |a| * |b| * |c| * |d| by simpa using h3] at h_eq
      exact_mod_cast h_eq
    have h5 : |a| * |b| * |c| * |d| / (a * b * c * d) = (|a| / a) * (|b| / b) * (|c| / c) * (|d| / d) := by
      field_simp [ha1, hb1, hc1, hd1]
      <;> ring_nf <;> simp [abs_mul] <;> ring_nf
      all_goals try native_decide
      all_goals try positivity
    have h6 : (|a| / a) * (|b| / b) * (|c| / c) * (|d| / d) = -1 := by 
      rw [h5] at h4
      exact_mod_cast h4
    -- Now, we need to determine which combination of signs is possible to get the product -1. Either 1 negative or 3 negatives.
    -- The maximum value is 2, which occurs when there is 1 negative and 3 positives.
    -- Since we have derived that in each of the possible its combinations will give less or equal to 2.
    have h8 : |a| / a + |b| / b + |c| / c + |d| / d ≤ 2 := by
      rcases h2 with (ha | ha) <;> rcases h2b with (hb | hb) <;> rcases h2c with (hc | hc) <;> rcases h2d with (hd | hd) <;> 
      try { 
        simp only [ha, hb, hc, hd] at h6 ⊢ <;> 
        try { 
          norm_num at h6 ⊢ <;> try { tauto } 
        } 
        <;> try { 
          linarith 
        } 
      }
      all_goals try { 
        linarith 
      }
      all_goals try { 
        nlinarith 
        all_goals try { linarith } 
      }
    -- Now, use the equality and the inequality to show that x ≤ 2.
    linarith [hx_eq, h8]