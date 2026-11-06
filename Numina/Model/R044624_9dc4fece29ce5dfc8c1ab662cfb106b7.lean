import Mathlib

theorem number_theory_161728 {P : Polynomial ℤ} (hP : Odd (P.eval 0) ∧ Odd (P.eval 1)) :
    ¬∃ x : ℤ, P.eval x = 0 := by 
  intro h
  rcases h with ⟨x, hx⟩
  have h1 : P.eval 0 % 2 = 1 := by 
    have h1 : Odd (P.eval 0) := hP.left
    obtain ⟨k, hk⟩ := h1
    omega
  have h2 : P.eval 1 % 2 = 1 := by 
    have h2 : Odd (P.eval 1) := hP.right
    obtain ⟨k, hk⟩ := h2
    omega
  have h4 : (P.eval x) % 2 = 1 := by 
    have h3 : x % 2 = 0 ∨ x % 2 = 1 := by 
      omega 
    rcases h3 with (h5 | h5)
    · -- Assume x is even 
      have h5' : x % 2 = 0 := h5 
      -- Show that $P(x) \equiv P(0) \ (\text{mod}\ 2)$.
      have h6 : (P.eval x : ℤ) % 2 = (P.eval 0 : ℤ) % 2 := by 
        have h7 : x % 2 = 0 := h5' 
        have h8 : (P.eval x) % 2 = (P.eval 0) % 2 := by 
          have h9 : (x : ℤ) % 2 = (0 : ℤ) % 2 := by omega 
          -- Show the congruence of powers
          have h11 : ∀ (n : ℕ), (x : ℤ) ^ n % 2 = (0 : ℤ) ^ n % 2 := by 
            intro n 
            have h12 : x % 2 = 0 := by omega 
            have h13 : ∀ (k : ℕ), (x : ℤ) ^ k % 2 = (0 : ℤ) ^ k % 2 := by 
              intro k 
              induction k with 
              | zero => 
                simp 
              | succ k ih => 
                simp [pow_succ, Int.mul_emod, h12, ih] 
            specialize h13 n 
            simpa using h13 
          -- Use computational facts for polynomial congruence.
          simp [Polynomial.eval_eq_sum_range, Finset.sum_int_mod, h11, Int.add_emod, Int.mul_emod] 
          <;> omega 
        exact h8 
      omega
    · -- Assume x is odd 
      have h5' : x % 2 = 1 := h5 
      -- Show that $P(x) \equiv P(1) \ (\text{mod}\ 2)$.
      have h6 : (P.eval x : ℤ) % 2 = (P.eval 1 : ℤ) % 2 := by 
        have h7 : x % 2 = 1 := h5' 
        have h8 : (P.eval x) % 2 = (P.eval 1) % 2 := by 
          have h9 : (x : ℤ) % 2 = (1 : ℤ) % 2 := by omega 
          -- Show the congruence of powers
          have h11 : ∀ (n : ℕ), (x : ℤ) ^ n % 2 = (1 : ℤ) ^ n % 2 := by 
            intro n 
            have h12 : x % 2 = 1 := by omega 
            have h13 : ∀ (k : ℕ), (x : ℤ) ^ k % 2 = (1 : ℤ) ^ k % 2 := by 
              intro k 
              induction k with 
              | zero => 
                simp 
              | succ k ih => 
                simp [pow_succ, Int.mul_emod, h12, ih] 
            specialize h13 n 
            simpa using h13 
          -- Use computational facts for polynomial congruence.
          simp [Polynomial.eval_eq_sum_range, Finset.sum_int_mod, h11, Int.add_emod, Int.mul_emod] 
          <;> omega 
        exact h8 
      omega 
  have h5 : (P.eval x : ℤ) % 2 = 0 := by 
    omega 
  omega