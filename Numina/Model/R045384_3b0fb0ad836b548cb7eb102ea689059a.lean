import Mathlib

theorem number_theory_292700 (x y : ℕ) (hx : x > 0) (hy : y > 0)
    (h : x^2 - 2 * y.factorial = 2021) :
    (x, y) = (45, 2) := by
  have h1 : x^2 = 2021 + 2 * y.factorial := by
    omega 
  have h2 : y ≤ 6 := by
    by_contra h3 
    push_neg at h3 
    have h3' : y ≥ 7 := by linarith
    have h7 : y.factorial % 7 = 0 := by
      have h8 : y ≥ 7 := h3'
      have h9 : ∀ (k : ℕ), (7 + k).factorial % 7 = 0 := by
        intro k 
        have h10 : (7 + k).factorial % 7 = 0 := by 
          have h11 : 7 ∣ (7 + k).factorial := by 
            apply Nat.dvd_factorial
            all_goals omega 
          have h12 : (7 + k).factorial % 7 = 0 := by
            omega 
          exact h12
        exact h10 
      specialize h9 (y - 7)
      have h10 : 7 + (y - 7) = y := by 
        omega 
      rw [h10] at h9 
      exact h9
    have h5 : x^2 % 7 = 5 := by
      omega 
    have h6 : x % 7 = 0 ∨ x % 7 = 1 ∨ x % 7 = 2 ∨ x % 7 = 3 ∨ x % 7 = 4 ∨ x % 7 = 5 ∨ x % 7 = 6 := by 
      omega 
    rcases h6 with (h | h | h | h | h | h | h) <;> 
      simp [Nat.pow_mod, h, Nat.mul_mod] at h5 
  interval_cases y <;> try { 
    norm_num [Nat.factorial] at h1 
    all_goals 
      { 
        have h4 : x ≤ 112 := by 
          nlinarith 
        interval_cases x <;> norm_num at h1 
          <;> tauto 
      }
  }