import Mathlib

theorem algebra_264529 {a b c d : ℤ} (ha : a > b) (hb : b > c) (hc : c > d)
    (hsum : a + b + c + d = 71) (h : (a - b) * (c - d) + (a - d) * (b - c) = 26) :
    a = 22 ∧ b = 21 ∧ c = 20 ∧ d = 8 := by

  have h1 : (a - c) * (b - d) = 26 := by
    nlinarith

  have h2 : a - c > 0 := by
    omega

  have h3 : b - d > 0 := by
    omega

  have h4 : a - c ∣ 26 := by
    use b - d
    linarith

  have h5 : a - c ≤ 26 := by
    apply Int.le_of_dvd (by norm_num) h4

  have h6 : a - c = 1 ∨ a - c = 2 ∨ a - c = 13 ∨ a - c = 26 := by
    interval_cases h7 : a - c <;> omega

  rcases h6 with h6 | h6 | h6 | h6

  · -- Case a - c = 1
    have h7 : b - d = 26 := by
      rw [h6] at h1
      nlinarith

    have h8 : a = c + 1 := by
      omega

    have h9 : b = d + 26 := by
      omega

    have h10 : c + d = 22 := by
      linarith [hsum, h8, h9]

    omega

  · -- Case a - c = 2
    have h7 : b - d = 13 := by
      rw [h6] at h1
      nlinarith

    have h8 : a = c + 2 := by
      omega

    have h9 : b = d + 13 := by
      omega

    have h10 : c + d = 28 := by
      linarith [hsum, h8, h9]

    have h11 : d = 8 := by
      omega

    have h12 : c = 20 := by
      omega

    have h13 : b = 21 := by
      omega

    have h14 : a = 22 := by
      omega

    exact ⟨h14, h13, h12, h11⟩

  · -- Case a - c = 13
    have h7 : b - d = 2 := by
      rw [h6] at h1
      nlinarith

    have h8 : a = c + 13 := by
      omega

    have h9 : b = d + 2 := by
      omega

    have h10 : c + d = 28 := by
      linarith [hsum, h8, h9]

    omega

  · -- Case a - c = 26
    have h7 : b - d = 1 := by
      rw [h6] at h1
      nlinarith

    have h8 : a = c + 26 := by
      omega

    have h9 : b = d + 1 := by
      omega

    have h10 : c + d = 22 := by
      linarith [hsum, h8, h9]

    omega