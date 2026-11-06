import Mathlib

theorem algebra_2639 {p q s t : ℝ} (hp : p ≠ 0) (hq : p = -q)
    (hs : s ≠ 0) (ht : s = 1 / t) :
    (p^3 + q^3) / (p^3 - q^3) - (s + t) / (s^2 * t + s * t^2) = -1 := by

  have h1 : q = -p := by
    linarith
  
  have h2 : p^3 + q^3 = 0 := by 
    rw [show q = -p by linarith]
    ring

  have h3 : p^3 - q^3 = 2 * p^3 := by 
    rw [show q = -p by linarith]
    ring

  have h4 : (p^3 + q^3) / (p^3 - q^3) = 0 := by 
    rw [h2, h3]
    field_simp [show p ^ 3 ≠ 0 by
      intro h'
      have : p = 0 := by 
        have h'1 : p ^ 3 = 0 := by linarith
        simp at h'1 ⊢
        all_goals nlinarith
      contradiction
    ]

  have htne : t ≠ 0 := by 
    by_contra h
    have h0 : s = 0 := by 
      rw [ht]
      field_simp [h]
    contradiction

  have h6 : s * t = 1 := by
    rw [ht]
    field_simp [htne]

  have h7 : s^2 * t + s * t^2 = (s * t) * (s + t) := by
    ring

  have h8 : s^2 * t + s * t^2 = s + t := by
    rw [h7, h6]
    all_goals
      ring

  have h9 : s + t ≠ 0 := by
    by_contra h
    have h10 : t = -s := by
      linarith

    have h11 : s * t = - (s ^ 2) := by 
      rw [h10]
      ring

    have h12 : s * t = 1 := h6

    have h13 : - (s ^ 2) = 1 := by
      linarith [h11, h12]

    have h14 : s ^ 2 ≥ 0 := sq_nonneg s

    nlinarith

  have h10 : (s + t) / (s^2 * t + s * t^2) = 1 := by
    rw [h8]
    field_simp [h9]

  rw [h4, h10]
  all_goals
    norm_num