import Mathlib

theorem number_theory_136862 :
    {(x, y) : ℤ × ℤ | x^3 + 2 * x * y - 7 = 0} =
    {(-7, -25), (-1, -4), (1, 3), (7, -24)} := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- Forward: if $(x, y)$ is in the set, then it's in $\{ (-7, -25), (-1, -4), (1, 3), (7, -24) \}$
    intro h
    have h_eq : x^3 + 2 * x * y - 7 = 0 := by 
      linarith
    have h1 : x ≠ 0 := by 
      by_contra h2
      rw [h2] at h_eq
      -- Show contradiction as $7 \neq 0$
      nlinarith
    have h2 : x ∣ 7 := by
      have h_eq' : x * (x^2 + 2 * y) = 7 := by
        nlinarith
      have : x ∣ 7 := by
        use (x^2 + 2 * y)
        linarith
      exact_mod_cast this
    have h3 : x = 1 ∨ x = -1 ∨ x = 7 ∨ x = -7 := by
      have h4 : x ∣ 7 := h2
      -- Verify the integer divisors of 7
      have h5 : x = 1 ∨ x = -1 ∨ x = 7 ∨ x = -7 := by
        have h6 : x ≤ 7 := by
          apply Int.le_of_dvd (by norm_num) h4
        have h7 : -7 ≤ x := by
          have h8 : -x ∣ 7 := by
            exact Int.neg_dvd.2 h4
          have h9 : -x ≤ 7 := by
            apply Int.le_of_dvd (by norm_num) h8
          linarith
        interval_cases x <;> tauto
      exact h5
    rcases h3 with (r1 | r1 | r1 | r1)
    · -- Case $x = 1$
      rw [r1] at h_eq
      have hy1 : y = 3 := by
        nlinarith
      simp [r1, hy1]
    · -- Case $x = -1$
      rw [r1] at h_eq
      have hy1 : y = -4 := by
        nlinarith
      simp [r1, hy1]
    · -- Case $x = 7$
      rw [r1] at h_eq
      have hy1 : y = -24 := by
        nlinarith
      simp [r1, hy1]
    · -- Case $x = -7$
      rw [r1] at h_eq
      have hy1 : y = -25 := by
        nlinarith
      simp [r1, hy1]
  · -- Backward: if $(x, y)$ is in $\{ (-7, -25), (-1, -4), (1, 3), (7, -24) \}$, then it's in the set
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · norm_num
    · norm_num
    · norm_num
    · norm_num