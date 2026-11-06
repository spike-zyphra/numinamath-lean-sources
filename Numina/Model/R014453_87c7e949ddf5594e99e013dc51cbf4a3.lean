import Mathlib

theorem algebra_241729 (a d : ℚ) (h₀ : a > 0) (h₁ : d > 0)
    (h₂ : ∃ m : ℕ, a + (a + d) + (a + 2 * d) = m)
    (h₃ : ∃ n : ℕ, a + (a + d) + (a + 2 * d) + (a + 3 * d) +
      (a + 4 * d) + (a + 5 * d) + (a + 6 * d) = n)
    (h₄ : a ≥ 1 / 3) :
    a ≥ 5 / 14 := by 
  rcases h₂ with ⟨m, hm⟩
  rcases h₃ with ⟨n, hn⟩
  have eq1 : 3 * a + 3 * d = (m : ℚ) := by
    linarith 
  have eq3 : 7 * a + 21 * d = (n : ℚ) := by
    linarith 
  have eq4 : a + d = (m : ℚ) / 3 := by
    linarith 
  have eq5 : a + 3 * d = (n : ℚ) / 7 := by 
    linarith 
  have eq6 : a = (7 * (m : ℚ) - (n : ℚ) ) / 14 := by 
    linarith [eq4, eq5]
  have eq7 : (7 * m - n : ℤ) ≥ (5 : ℤ) := by 
    have h8 : (m : ℚ) * (21 : ℚ) - (n : ℚ) * (3 : ℚ) ≥ (14 : ℚ) := by
      have h5 : (7 * (m : ℚ) - (n : ℚ) ) / 14 ≥ (1 / 3 : ℚ) := by
        linarith [show (a : ℚ) ≥ (1 / 3 : ℚ) from h₄, eq6]
      linarith [h5] 
    have h9 : (21 * (m : ℤ) - 3 * (n : ℤ) ) ≥ (14 : ℤ) := by
      have h10 : (21 * (m : ℤ) - 3 * (n : ℤ) ) ≥ (14 : ℤ) := by
        have h11 : (m : ℚ) * (21 : ℚ) - (n : ℚ) * (3 : ℚ) = ((21 * (m : ℤ) - 3 * (n : ℤ) ) : ℚ) := by 
          simp
          <;> ring
        have h12 : ((21 * (m : ℤ) - 3 * (n : ℤ) ) : ℚ) ≥ (14 : ℚ) := by
          linarith [h11, h8]
        have h13 : (21 * (m : ℤ) - 3 * (n : ℤ) ) ≥ (14 : ℤ) := by 
          exact_mod_cast h12
        assumption 
      assumption 
    omega 
  have eq8 : a ≥ (5 / 14 : ℚ) := by
    rw [eq6]
    have h11 : (7 * (m : ℚ) - (n : ℚ) ) ≥ (5 : ℚ) := by
      have h14 : (7 * m - n : ℤ) ≥ (5 : ℤ) := by 
        omega 
      have h15 : (7 * (m : ℚ) - (n : ℚ) ) ≥ (5 : ℚ) := by
        exact_mod_cast h14 
      linarith 
    linarith 
  linarith [eq8, h₄]