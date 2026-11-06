import Mathlib

theorem algebra_233792 (k : ℕ) (P : ℤ → ℤ)
    (hP : ∀ x, P x = x^1998 - x^1996 + x^4 - 3 * k * x + 3 * x + 1) :
    ∀ n, P n ≠ 0 := by
  intro n
  have h1 : P n = n ^ 1998 - n ^ 1996 + n ^ 4 - 3 * k * n + 3 * n + 1 := by
    specialize hP n
    simpa using hP
  rw [h1]
  by_contra h
  have eq4 : n ∣ 1 := by
    have eq5 : n ^ 1998 - n ^ 1996 + n ^ 4 - 3 * k * n + 3 * n + 1 = 0 := by
      omega
    have eq6 : n ∣ (n ^ 1998 - n ^ 1996 + n ^ 4 + 3 * n + 1 : ℤ) := by
      have h7 : (n ^ 1998 - n ^ 1996 + n ^ 4 + 3 * n + 1 : ℤ) = 3 * (k : ℤ) * n := by 
        nlinarith [eq5]
      have eq8 : n ∣ (3 * (k : ℤ) * n) := by 
        use 3 * (k : ℤ)
        all_goals ring
      rw [h7] at *
      exact eq8
    have eq8 : n ∣ (n ^ 1998 - n ^ 1996 + n ^ 4 + 3 * n : ℤ) := by
      use (n ^ 1997 - n ^ 1995 + n ^ 3 + 3)
      all_goals 
        ring
    have eq9 : n ∣ ((n ^ 1998 - n ^ 1996 + n ^ 4 + 3 * n + 1) - (n ^ 1998 - n ^ 1996 + n ^ 4 + 3 * n)) := by
      apply Dvd.dvd.sub 
      · exact eq6 
      · exact eq8 
    have eq12 : ((n ^ 1998 - n ^ 1996 + n ^ 4 + 3 * n + 1) - (n ^ 1998 - n ^ 1996 + n ^ 4 + 3 * n)) = 1 := by
      ring
    rw [eq12] at eq9 
    exact eq9 
  have eq5 : n = 1 ∨ n = -1 := by 
    have h2 : n ∣ 1 := eq4
    have h3 : n ≤ 1 := by 
      apply Int.le_of_dvd (show 0 < 1 by norm_num) h2 
    have h4 : n ≥ -1 := by 
      have h5 : -n ∣ 1 := by 
        exact Int.neg_dvd.2 h2 
      have h6 : -n ≤ 1 := by 
        apply Int.le_of_dvd (show 0 < 1 by norm_num) h5 
      omega 
    interval_cases n <;> try { 
      omega
    }
  rcases eq5 with (r | r)
  · --n = 1
    rw [show n = 1 by linarith [r]] at h 
    exfalso 
    have eq6 : (1 : ℤ) ^ 1998 - (1 : ℤ) ^ 1996 + (1 : ℤ) ^ 4 - 3 * k * (1 : ℤ) + 3 * (1 : ℤ) + 1 = 0 := by 
      nlinarith [h] 
    omega 
  · --n = -1
    rw [show n = -1 by linarith [r]] at h
    exfalso 
    have eq7 : (-1 : ℤ) ^ 1998 - (-1 : ℤ) ^ 1996 + (-1 : ℤ) ^ 4 - 3 * k * (-1 : ℤ) + 3 * (-1 : ℤ) + 1 = 0 := by
      nlinarith [h] 
    omega