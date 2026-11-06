import Mathlib

theorem number_theory_119976 : Set.Infinite {x : ℚ | ⌊x⌋ * (x - ⌊x⌋) = 2013 / 2014} := by
  apply Set.infinite_of_injective_forall_mem (f := λ (n : ℕ) => (↑n + 2 : ℚ) + (2013 / (2014 : ℚ)) / (↑n + 2 : ℚ))
  · -- Show f is injective
    intro n m h
    have h1 : (↑n + 2 : ℚ) + (2013 / (2014 : ℚ)) / (↑n + 2 : ℚ) = (↑m + 2 : ℚ) + (2013 / (2014 : ℚ)) / (↑m + 2 : ℚ) := by
      simpa using h
    have h2 : (↑n : ℚ) = (↑m : ℚ) := by
      have eq1 : ((↑n + 2 : ℚ) + (2013 / (2014 : ℚ)) / (↑n + 2 : ℚ)) - ((↑m + 2 : ℚ) + (2013 / (2014 : ℚ)) / (↑m + 2 : ℚ)) = 0 := by
        linarith [h1]
      have eq2 : ((↑n + 2 : ℚ) + (2013 / (2014 : ℚ)) / (↑n + 2 : ℚ)) - ((↑m + 2 : ℚ) + (2013 / (2014 : ℚ)) / (↑m + 2 : ℚ)) =
          (↑n - (↑m : ℚ)) + ((2013 / (2014 : ℚ)) / (↑n + 2) - (2013 / (2014 : ℚ)) / (↑m + 2))
          := by ring
      rw [eq2] at eq1
      have eq3 : (↑n - (↑m : ℚ)) * (1 - (2013 / (2014 : ℚ)) / ((↑n + 2 : ℚ) * (↑m + 2 : ℚ))) = 0 := by
        field_simp [(show (↑n + 2 : ℚ) ≠ 0 by positivity), 
                    (show (↑m + 2 : ℚ) ≠ 0 by positivity)] at eq1 ⊢
        nlinarith 
      cases' (mul_eq_zero.mp eq3) with h_eq4 h_eq5
      · -- Case h_eq4
        linarith 
      · -- Case h_eq5
        field_simp [(show (↑n + 2 : ℚ) ≠ 0 by positivity), 
                    (show (↑m + 2 : ℚ) ≠ 0 by positivity)] at h_eq5 ⊢
        nlinarith [show (↑n : ℚ) ≥ 0 by positivity, 
                show (↑m : ℚ) ≥ 0 by positivity, 
                mul_nonneg (show (↑n : ℚ) ≥ 0 by positivity) (show (↑m : ℚ) ≥ 0 by positivity)]
    have h_eq7 : n = m := by 
      exact_mod_cast h2 
    exact h_eq7 
  · -- Show that all elements of the image of f are in the set
    intro n 
    simp only [Set.mem_setOf_eq]
    have hfloor : ⌊(↑n + 2 : ℚ) + (2013 / 2014) / (↑n + 2 : ℚ)⌋ = (n + 2 : ℤ) := by
      simp [Int.floor_eq_iff]
      all_goals
      have h1 : (2013 / (2014 : ℚ) ) / (↑n + 2 : ℚ) ≥ 0 := by 
        apply div_nonneg 
        · norm_num
        · positivity 
      have h2 : (2013 / (2014 : ℚ) ) / (↑n + 2 : ℚ) < (1 : ℚ) := by 
        have hn1 : (↑n + 2 : ℚ) ≥ (2 : ℚ) := by 
          have h1 : (↑n : ℚ) ≥ 0 := by positivity 
          linarith 
        have h3 : (2013 / (2014 : ℚ)) / (↑n + 2 : ℚ) < (1 : ℚ) := by 
          apply (div_lt_iff₀ (by positivity)).mpr 
          nlinarith [show (↑n + 2 : ℚ) ≥ (2 : ℚ) by linarith, 
            mul_nonneg (show (↑n : ℚ) ≥ 0 by positivity) (show (↑n : ℚ) ≥ 0 by positivity)]
        linarith 
      constructor 
      · -- Show that n + 2 ≤ x 
        linarith 
      · -- Show that x < n + 2 + 1 
        linarith 
    rw [hfloor]
    have eq1 : ((n + 2 : ℤ) : ℚ) * ((↑n + 2 + (2013 / 2014) / (↑n + 2) ) - ↑(n + 2 : ℤ)) = (2013 / 2014 : ℚ) := by 
      have h2n : (↑(n + 2 : ℤ) : ℚ) = (↑n + 2 : ℚ) := by 
        simp 
      rw [h2n]
      field_simp [(show (↑n + 2 : ℚ) ≠ 0 by positivity)]
      <;> ring_nf 
      <;> field_simp [(show (↑n + 2 : ℚ) ≠ 0 by positivity)]
      <;> ring 
    simpa using eq1