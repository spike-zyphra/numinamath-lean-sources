import Mathlib

theorem algebra_246156 {a b c t : ℝ} (ha : a ≠ 0) (ht : t ≠ 0)
    (hvertex : ∀ x, a * x ^ 2 + b * x + c = a * (x - t) ^ 2 + t)
    (hpoint : a * (-t) ^ 2 + b * (-t) + c = -t) :
    a ^ 2 + b ^ 2 + c ^ 2 = 33 / 16 ↔ t = -2 ∨ t = -1 / 2 ∨ t = 1 / 2 ∨ t = 2 := by

  have h5 := hvertex 0
  have h6 : c = a * t ^ 2 + t := by
    nlinarith

  have h7 := hvertex 1 
  have h8 := hvertex (-1)
  have h2 : b = -2 * a * t := by
    have eq1 := hvertex 1
    have eq2 := hvertex (-1)
    nlinarith

  have h8 : c = a * t ^ 2 + t := by
    nlinarith

  have h9 : 4 * a * t ^ 2 = -2 * t := by
    rw [h2] at hpoint
    rw [h6] at hpoint
    nlinarith

  have h10 : 2 * a * t + 1 = 0 := by 
    apply (mul_left_inj' ht).mp
    linarith

  have r1 : a * t = -1 / 2 := by
    linarith

  have hb_eq : b = 1 := by
    have r1' : a * t = -1 / 2 := r1
    have h2' : b = -2 * a * t := h2
    calc
      b = -2 * (a * t) := by 
        rw [h2']
        <;> ring 
      _ = -2 * (-1 / 2) := by 
        rw [r1']
      _ = 1 := by 
        norm_num

  have hc_eq : c = t / 2 := by 
    have r1' : a * t = -1 / 2 := r1 
    have hc : c = a * t ^ 2 + t := h6 
    calc 
      c = a * t ^ 2 + t := by 
        linarith [hc] 
      _ = (a * t) * t + t := by 
        ring 
      _ = (-1 / 2) * t + t := by 
        rw [r1']
      _ = t / 2 := by
        linarith

  have h3 : a ^ 2 + b ^ 2 + c ^ 2 = (1 / (4 * t ^ 2)) + 1 + (t ^ 2 / 4) := by
    have h2' : a = -1 / (2 * t) := by
      field_simp at *
      nlinarith 
      <;> field_simp [ht]
    rw [show a = -1 / (2 * t) by 
      field_simp at *
      linarith 
    ]
    rw [hb_eq]
    rw [hc_eq]
    field_simp [ht, show t ^ 2 > 0 by positivity]
    ring

  rw [h3]
  constructor
  · -- Assume `N` prove `M`, where `N` is the quadratic expression and `M` the value.
    intro h
    have h1 : 4 * t ^ 4 - 17 * t ^ 2 + 4 = 0 := by
      have h11 : t ≠ 0 := ht 
      have eq1 : (1 / (4 * t ^ 2)) + 1 + (t ^ 2 / 4) = 33 / 16 := by 
        simpa using h
      have h12 : t ^ 2 > 0 := by 
        exact sq_pos_of_ne_zero ht 
      field_simp at eq1
      nlinarith 
    have h2 : (t ^ 2 - 4) * (t ^ 2 - 1 / 4) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- First case: t^2 - 4 = 0
      have ht1 : t ^ 2 = 4 := by 
        nlinarith
      have ht2 : t = 2 ∨ t = -2 := by 
        have h1 : t ^ 2 = 4 := ht1
        have : t = 2 ∨ t = -2 := by 
          apply eq_or_eq_neg_of_sq_eq_sq 
          norm_num 
          linarith 
        assumption 
      cases' ht2 with h4 h5
      · 
        right 
        right 
        right 
        tauto 
      · 
        left 
        tauto
    · -- Second case: t^2 - 1/4 = 0 
      have ht1 : t ^ 2 = 1 / 4 := by
        nlinarith 
      have ht2 : t = 1 / 2 ∨ t = -1 / 2 := by 
        have h1 : t ^ 2 = 1 / 4 := ht1 
        have : t = 1 / 2 ∨ t = -1 / 2 := by 
          have h2 : t^2 - (1/4) = 0 := by 
            linarith 
          have h3 : (t - 1/2) * (t + 1/2) = 0 := by
            nlinarith 
          cases' (mul_eq_zero.mp h3) with h4 h5 
          · 
            left 
            linarith 
          · 
            right 
            linarith 
        assumption 
      cases' ht2 with h6 h7 
      · 
        right 
        right 
        left 
        tauto 
      · 
        right 
        left 
        tauto 
  · -- Assume M prove N.
    rintro (h | h | h | h)
    · -- Case t = -2 
      rw [h] 
      norm_num 
    · -- Case t = -1/2 
      rw [h] 
      norm_num 
    · -- Case t = 1/2 
      rw [h] 
      norm_num 
    · -- Case t = 2 
      rw [h] 
      norm_num