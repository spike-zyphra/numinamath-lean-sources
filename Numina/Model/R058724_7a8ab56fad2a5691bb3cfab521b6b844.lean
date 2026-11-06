import Mathlib

theorem algebra_2086 {a b c d : ℚ} (habcd : a ≠ 1997 ∧ b ≠ -1998 ∧ c ≠ 1999 ∧ d ≠ -2000 ∧ 1 / (a - 1997) = 1 / (b + 1998) ∧ 1 / (b + 1998) = 1 / (c - 1999) ∧ 1 / (c - 1999) = 1 / (d + 2000)) : c > a ∧ a > b ∧ b > d := by

  rcases habcd with ⟨ha, hb, hc, hd, h1, h2, h3⟩

  have eq1 : b + 1998 = a - 1997 := by
    have h1' : a - 1997 ≠ 0 := by
      intro h
      apply ha
      linarith
    have h1'' : b + 1998 ≠ 0 := by
      intro h
      apply hb
      linarith
    field_simp [h1', h1''] at h1 ⊢
    linarith

  have ha_eq : a = b + 3995 := by
    linarith [eq1]

  have eq2 : c - 1999 = b + 1998 := by
    have h2' : b + 1998 ≠ 0 := by
      intro h
      apply hb
      linarith
    have h2'' : c - 1999 ≠ 0 := by
      intro h
      apply hc
      linarith
    field_simp [h2', h2''] at h2 ⊢
    linarith

  have hc_eq : c = b + 3997 := by
    linarith [eq2]

  have eq3 : d + 2000 = c - 1999 := by
    have h3' : c - 1999 ≠ 0 := by
      intro h
      apply hc
      linarith
    have h3'' : d + 2000 ≠ 0 := by
      intro h
      apply hd
      linarith
    field_simp [h3', h3''] at h3 ⊢
    linarith

  have hd_eq : d = b - 2 := by
    rw [hc_eq] at eq3
    linarith [eq3]

  have h_c_a : c > a := by
    rw [hc_eq, ha_eq]
    linarith

  have h_a_b : a > b := by
    linarith [ha_eq]

  have h_b_d : b > d := by
    linarith [hd_eq]

  exact ⟨h_c_a, h_a_b, h_b_d⟩