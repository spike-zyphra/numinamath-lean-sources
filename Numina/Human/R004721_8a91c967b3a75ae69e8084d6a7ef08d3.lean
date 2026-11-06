import Mathlib

open Real

theorem algebra_310800 (A : ℝ) (hA : A > 0) :
  {(x, y) : ℝ × ℝ | y = A * x ^ 2 ∧ y ^ 2 + 3 = x ^ 2 + 4 * y}.encard = 4 := by


  let a := 1 / A
  have ha : a > 0 := by positivity
  let S := {(x, y) : ℝ × ℝ | y = A * x ^ 2 ∧ y ^ 2 + 3 = x ^ 2 + 4 * y}

  let y1 := a/2+2-√(a^2+8*a+4)/2
  let y2 := a/2+2+√(a^2+8*a+4)/2

  let x1 := √(a*y1)

  have h_y1_pos : y1 > 0 := by
    unfold y1
    suffices √(a ^ 2 + 8 * a + 4) < a + 4 by linarith
    rw [sqrt_lt]
    all_goals nlinarith

  have hx1 : y1 = A * x1 ^ 2 := by
    unfold x1
    rw [sq_sqrt (by nlinarith)]
    unfold a
    field_simp

  have hx1' : y1 = A * (-x1) ^ 2 := by
    rw [hx1]
    ring_nf

  have hy1 : y1 ^ 2 + 3 = x1 ^ 2 + 4 * y1 := by
    have : x1 ^ 2 = a * y1 := by
      rw [hx1]
      unfold a
      field_simp
    rw [this]
    unfold y1
    suffices ∀ a > 0, (a / 2 + 2 - √(a ^ 2 + 8 * a + 4) / 2) ^ 2 + 3 = a * (a / 2 + 2 - √(a ^ 2 + 8 * a + 4) / 2) + 4 * (a / 2 + 2 - √(a ^ 2 + 8 * a + 4) / 2) by
      exact this a ha

    intro t ht
    ring_nf
    rw [sq_sqrt (by positivity)]
    ring_nf


  have hy1' : y1 ^ 2 + 3 = (-x1) ^ 2 + 4 * y1 := by
    rw [hy1]
    ring_nf

  let x2 := √(a*y2)

  have hx2 : y2 = A * x2 ^ 2 := by
    unfold x2
    rw [sq_sqrt (by positivity)]
    unfold a
    field_simp

  have hx2' : y2 = A * (-x2) ^ 2 := by
    rw [hx2]
    ring_nf

  have hy2 : y2 ^ 2 + 3 = x2 ^ 2 + 4 * y2 := by
    have : x2 ^ 2 = a * y2 := by
      rw [hx2]
      unfold a
      field_simp
    rw [this]
    unfold y2
    suffices ∀ a > 0, (a / 2 + 2 + √(a ^ 2 + 8 * a + 4) / 2) ^ 2 + 3 = a * (a / 2 + 2 + √(a ^ 2 + 8 * a + 4) / 2) + 4 * (a / 2 + 2 + √(a ^ 2 + 8 * a + 4) / 2) by
      exact this a ha

    intro t ht
    ring_nf
    rw [sq_sqrt (by positivity)]
    ring_nf

  have hy2' : y2 ^ 2 + 3 = (-x2) ^ 2 + 4 * y2 := by
    rw [hy2]
    ring_nf

  suffices S = {(x1, y1), (-x1, y1), (x2, y2), (-x2, y2)} by
    unfold S at this
    rw [this]

    have h_y2_pos : y2 > 0 := by positivity
    have h_x1_pos : x1 > 0 := by positivity
    have h_x2_pos : x2 > 0 := by positivity
    have : ¬y1 = y2 := by
      by_contra h
      unfold y1 y2 at h
      have : √(a ^ 2 + 8 * a + 4) = 0 := by linarith
      rw [sqrt_eq_zero (by positivity)] at this
      nlinarith

    have h1 : (x1, y1) ∉ ({(-x1, y1), (x2, y2), (-x2, y2)} : Set (ℝ × ℝ)) := by
      simp
      constructor
      . linarith
      tauto

    have h2 : (-x1, y1) ∉ ({(x2, y2), (-x2, y2)} : Set (ℝ × ℝ)) := by
      simp
      tauto


    have h3 : (x2, y2) ∉ ({(-x2, y2)} : Set (ℝ × ℝ)) := by
      simp
      linarith

    rw [Set.encard_insert_of_not_mem h1]
    rw [Set.encard_insert_of_not_mem h2]
    rw [Set.encard_insert_of_not_mem h3]
    simp
    norm_num


  ext ⟨x, y⟩
  constructor
  . intro h
    unfold S at h
    simp
    simp at h
    have ⟨h1, h2⟩ := h
    have : x ^ 2 = a * y := by
      rw [h1]
      unfold a
      field_simp


    rw [this] at h2
    have h2 : y ^ 2 = a * y + 4 * y - 3 := by linarith
    have : (y-y1)*(y-y2) = 0 := by
      ring_nf
      rw [show A⁻¹ = a by unfold a; field_simp]
      rw [sq_sqrt (by positivity)]
      rw [h2]
      ring_nf

    simp at this
    rcases this with h | h
    . have : y = y1 := by linarith
      rw [this] at h1
      rw [h1] at hx1
      have : A*(x-x1)*(x+x1) = 0 := by linarith
      simp at this
      rcases this with h | h
      . rcases h with h | h
        . linarith
        . have : x = x1 := by linarith
          tauto
      . have : x = -x1 := by linarith
        tauto

    . have : y = y2 := by linarith
      rw [this] at h1
      rw [h1] at hx2
      have : A*(x-x2)*(x+x2) = 0 := by linarith
      simp at this
      rcases this with h | h
      . rcases h with h | h
        . linarith
        . have : x = x2 := by linarith
          tauto
      . have : x = -x2 := by linarith
        tauto


  . intro h
    unfold S
    simp
    simp at h
    rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
    all_goals
    . subst x y
      tauto
