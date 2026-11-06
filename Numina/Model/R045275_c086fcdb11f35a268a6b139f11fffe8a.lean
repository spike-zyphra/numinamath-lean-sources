import Mathlib

theorem algebra_2966 {n : ℕ} {a d : ℤ} (h : ∑ i ∈ Finset.range (n + 1), (a + d * (2 * i)) = ∑ i ∈ Finset.range n, (a + d * (2 * i + 1))) :
    ∑ i ∈ Finset.range (2 * n + 1), (a + d * i) = 0 := by
  have eq1 : ∀ (n : ℕ), ∑ i ∈ Finset.range (n + 1), (a + d * (2 * (i : ℤ)) : ℤ) = (n + 1 : ℤ) * a + (n : ℤ) * (n + 1 : ℤ) * d := by
    intro n 
    induction n with 
    | zero =>
      simp 
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp [mul_add, add_mul]
      <;> ring
  -- Prove the formula for the right side using induction
  have eq2 : ∀ (n : ℕ), ∑ i ∈ Finset.range (n : ℕ), (a + d * (2 * (i : ℤ) + 1) : ℤ) = (n : ℤ) * a + (n : ℤ) * (n : ℤ) * d := by 
    intro n 
    induction n with
    | zero =>
      simp 
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp [mul_add, add_mul]
      <;> ring 
  -- Use equality of sum to find relationship between a and d 
  have eq3 : a + (n : ℤ) * d = 0 := by
    have eq4 : ∑ i ∈ Finset.range (n + 1), (a + d * (2 * (i : ℤ)) ) = (n + 1 : ℤ) * a + (n : ℤ) * (n + 1 : ℤ) * d := by 
      specialize eq1 n 
      simpa using eq1 
    have eq5 : ∑ i ∈ Finset.range n, (a + d * (2 * (i : ℤ) + 1) ) = (n : ℤ) * a + (n : ℤ) * (n : ℤ) * d := by 
      specialize eq2 n 
      simpa using eq2 
    rw [eq4, eq5] at h 
    -- Simplify h to prove a + n * d = 0
    have eq6 : (n + 1 : ℤ) * a + (n : ℤ) * (n + 1 : ℤ) * d = (n : ℤ) * a + (n : ℤ) * (n : ℤ) * d := by 
      linarith -- Simplify the equation from h 
    -- From eq6 derive a + n * d = 0 
    have eq7 : a + (n : ℤ) * d = 0 := by 
      nlinarith 
    exact_mod_cast eq7
  -- Prove the formula for the total sum
  have eq6 : ∑ i ∈ Finset.range (2 * n + 1), (a + d * (i : ℤ)) = (2 * n + 1) * (a + (n : ℤ) * d) := by 
    have eq4 : ∀ (n : ℕ), ∑ i ∈ Finset.range (2 * n + 1), (a + d * (i : ℤ)) = (2 * n + 1) * (a + (n : ℤ) * d) := by
      intro n 
      induction n with 
      | zero =>
        norm_num 
      | succ n ih =>
        rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by omega] 
        rw [Finset.sum_range_succ, Finset.sum_range_succ, ih] 
        simp [mul_add, add_mul]
        <;> ring
    specialize eq4 n 
    simpa using eq4 
  -- Now, substitute eq3 into eq6 to get 0
  rw [eq6] 
  rw [eq3] 
  all_goals 
    norm_num