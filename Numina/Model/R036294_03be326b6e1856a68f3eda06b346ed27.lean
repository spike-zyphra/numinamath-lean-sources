import Mathlib

theorem algebra_91097 {x y : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) :
    (19 / x : ℚ) + (96 / y : ℚ) = (19 / x) * (96 / y) ↔
    ∃ m, x = 19 * m ∧ y = 96 - 96 * m := by
  constructor
  · -- Assume (19/x : ℚ) + (96/y : ℚ) = (19/x) * (96/y)
    intro h_eq
    have h1 : (19 : ℤ) * y + (96 : ℤ) * x = (19 * 96 : ℤ) := by
      have h2 : (19 : ℚ) * (y : ℚ) + (96 : ℚ) * (x : ℚ) = (19 * 96 : ℚ) := by
        have h3 : x ≠ 0 := by exact_mod_cast hx
        have h4 : y ≠ 0 := by exact_mod_cast hy
        field_simp [h3, h4] at h_eq ⊢
        nlinarith [h_eq]
      exact_mod_cast h2
    -- Show that x is divisible by 19
    have h5 : x % 19 = 0 := by
      omega
    have h4 : ∃ m, x = 19 * m := by
      refine' ⟨x / 19, by omega⟩
    rcases h4 with ⟨m, hm⟩
    -- From the equation, derive y = 96 - 96m
    have h6 : y = 96 - 96 * m := by
      nlinarith [hm, h1]
    -- Show the parametric solution
    exact ⟨m, by linarith, by linarith⟩
  · -- Assume ∃ m, x = 19 * m ∧ y = 96 - 96 * m
    rintro ⟨m, hx_eq, hy_eq⟩
    have h1 : (x : ℚ) = 19 * (m : ℚ) := by 
      exact_mod_cast hx_eq
    have h2 : (y : ℚ) = 96 - 96 * (m : ℚ) := by
      exact_mod_cast hy_eq
    have h3 : (19 : ℚ) / (x : ℚ) + (96 : ℚ) / (y : ℚ) = (19 / (x : ℚ)) * (96 / (y : ℚ)) := by
      rw [h1, h2]
      have h4 : (m : ℚ) ≠ 0 := by
        by_contra h
        have hm1 : m = 0 := by 
          have h7 : (m : ℚ) = 0 := by linarith
          exact_mod_cast h7
        rw [hm1] at hx_eq
        have hx0 : x = 0 := by 
          linarith
        contradiction
      have h5 : (96 - 96 * (m : ℚ)) ≠ 0 := by
        by_contra h
        have hm6 : (m : ℚ) = 1 := by
          nlinarith
        have hm6' : m = 1 := by
          exact_mod_cast hm6
        rw [hm6'] at hy_eq
        have hy0 : y = 0 := by 
          linarith
        contradiction
      field_simp [h4, h5]
      <;> ring_nf 
    simpa using h3