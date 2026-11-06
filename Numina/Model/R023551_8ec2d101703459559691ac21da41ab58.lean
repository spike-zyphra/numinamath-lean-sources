import Mathlib

theorem algebra_241923 {a d : ℚ} (h₀ : a > 0) (h₁ : d > 0)
    (h₂ : ∃ n : ℕ, a + (a + d) + (a + 2 * d) + (a + 3 * d) = n)
    (h₃ : ∃ m : ℕ, a + (a + d) + (a + 2 * d) + (a + 3 * d) + (a + 4 * d) +
      (a + 5 * d) + (a + 6 * d) + (a + 7 * d) + (a + 8 * d) = m)
    (h₄ : a ≤ 3 / 4) :
    a ≤ 11 / 15 := by
  rcases h₂ with ⟨n, hn⟩
  rcases h₃ with ⟨m, hm⟩
  have h2 : 4 * a + 6 * d = (n : ℚ) := by
    have h_eq : a + (a + d) + (a + 2 * d) + (a + 3 * d) = 4 * a + 6 * d := by 
      ring
    rw [h_eq] at hn
    exact_mod_cast hn
  have h3 : 9 * a + 36 * d = (m : ℚ) := by 
    have h_eq : a + (a + d) + (a + 2 * d) + (a + 3 * d) + (a + 4 * d) +
      (a + 5 * d) + (a + 6 * d) + (a + 7 * d) + (a + 8 * d) = 9 * a + 36 * d := by 
      ring
    rw [h_eq] at hm
    exact_mod_cast hm
  have eq1 : a = (6 * (n : ℚ) - (m : ℚ)) / 15 := by
    linarith [h2, h3]
  have h4 : (6 * (n : ℚ) - (m : ℚ)) ≤ 45 / 4 := by
    have h5 : (6 * (n : ℚ) - (m : ℚ)) / 15 ≤ (3 / 4 : ℚ) := by
      rw [eq1] at h₄
      linarith
    linarith
  have eq7 : (6 * (n : ℚ) - (m : ℚ)) = (6 * (n : ℤ) - (m : ℤ) : ℚ) := by
    have eq6 : (6 * (n : ℤ) - (m : ℤ) : ℚ) = (6 * (n : ℚ) - (m : ℚ) : ℚ) := by
      simp [sub_eq_add_neg, mul_add, add_mul]
      <;> norm_cast
      <;> ring_nf <;> norm_cast
    exact_mod_cast eq6
  have h7 : (6 * (n : ℚ) - (m : ℚ)) ≤ (11 : ℚ) := by
    have h8 : (6 * (n : ℚ) - (m : ℚ) : ℚ) = (6 * (n : ℤ) - (m : ℤ) : ℚ) := eq7
    have h9 : (6 * (n : ℚ) - (m : ℚ) : ℚ) ≤ (45 / 4 : ℚ) := h4
    have h10 : (6 * (n : ℤ) - (m : ℤ) : ℚ) ≤ (11 : ℚ) := by
      have h11 : (6 * (n : ℤ) - (m : ℤ)) ≤ 11 := by
        by_contra h
        push_neg at h
        have h12 : (6 * (n : ℤ) - (m : ℤ) : ℚ) ≥ (12 : ℚ) := by
          exact_mod_cast h
        nlinarith
      exact_mod_cast h11
    nlinarith
  have eq2 : a = (6 * (n : ℚ) - (m : ℚ)) / 15 := eq1
  linarith [eq2, h7]