import Mathlib

theorem algebra_186377 (x y z : ℕ) (hx : ∃ m, x = m^2) (hy : ∃ n, y = n^2) (hz : ∃ p, z = p^2)
    (h1 : x - y = 96) (h2 : y - z = 96) :
    (x, y, z) = (196, 100, 4) := by

  rcases hx with ⟨m, rfl⟩
  rcases hy with ⟨n, rfl⟩
  rcases hz with ⟨p, rfl⟩
  have eq1 : m^2 = n^2 + 96 := by
    omega
  have eq2 : n^2 = p^2 + 96 := by
    omega

  have h3 : m > n := by
    by_contra h
    push_neg at h
    have h4 : m ≤ n := by linarith
    have h5 : m^2 ≤ n^2 := by
      apply Nat.pow_le_pow_of_le_left
      all_goals linarith
    omega
  have h4 : n > p := by
    by_contra h
    push_neg at h
    have h6 : n ≤ p := by linarith
    have h7 : n^2 ≤ p^2 := by 
      apply Nat.pow_le_pow_of_le_left
      all_goals linarith
    omega

  have h5 : m ≤ 54 := by
    nlinarith [sq_nonneg (m : ℤ), sq_nonneg (n : ℤ)]
  have h9 : n ≤ 54 := by
    nlinarith [sq_nonneg (n : ℤ), sq_nonneg (p : ℤ)]
  have h10 : p ≤ 54 := by
    nlinarith [sq_nonneg (n : ℤ), sq_nonneg (p : ℤ)]

  have h8 : m ≤ 54 := h5
  have h11 : n ≤ 54 := h9
  have h12 : p ≤ 54 := h10

  simp [Prod.ext_iff] at *
  -- Now with upper and lower bounds, exhaustive search can determine unqeuilque solution
  interval_cases m <;> try { 
    interval_cases n <;> norm_num at eq1 eq2 
      <;> try { 
        interval_cases p 
        <;> norm_num at eq2 
        <;> tauto 
      }
  }
  <;> omega