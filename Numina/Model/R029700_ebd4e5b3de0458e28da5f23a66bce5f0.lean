import Mathlib

theorem number_theory_216350 :
    IsGreatest {n | n + 10 ∣ n ^ 3 + 100} 890 := by
  constructor 
  · -- Show that 890 is in the set.
    norm_num
  · -- Show that for any n in the set, n ≤ 890.
    intro n hn
    have h1 : n + 10 ∣ n ^ 3 + 100 := hn
    -- Prove that $n + 10$ divides $900$.
    have h2 : n + 10 ∣ 900 := by
      have eq1 : (n + 10 : ℤ) ∣ (n ^ 3 + 100 : ℤ) := by 
        exact_mod_cast h1
      -- We know that $n^3 + 1000 = (n + 10)(n^2 - 10n + 100)$.
      have eq2 : (n + 10 : ℤ) ∣ (n ^ 3 + 1000 : ℤ) := by
        use (n ^ 2 - 10 * n + 100 : ℤ)
        ring_nf
      -- Therefore, $n + 10$ divides $(n^3 + 1000) - (n^3 + 100) = 900$.
      have eq3 : (n + 10 : ℤ) ∣ ((n ^ 3 + 1000 : ℤ) - (n ^ 3 + 100 : ℤ)) := by
        apply Dvd.dvd.sub 
        · exact eq2 
        · exact eq1 
      -- Simplify the difference.
      have eq4 : ((n ^ 3 + 1000 : ℤ) - (n ^ 3 + 100 : ℤ)) = (900 : ℤ) := by
        ring_nf 
      -- Now we have $n + 10$ divides $900$.
      rw [eq4] at eq3
      -- Convert the divisibility from integer to natural numbers.
      have h3 : (n + 10 : ℕ) ∣ (900 : ℕ) := by 
        exact_mod_cast eq3 
      exact h3
    -- Now from $n + 10$ divides $900$, we can conclude $n + 10 \le 900$.
    have h3 : n + 10 ∣ 900 := h2 
    have h4 : n + 10 ≤ 900 := by 
      exact Nat.le_of_dvd (by linarith) h3 
    -- Therefore, $n \le 890$.
    have h5 : n ≤ 890 := by 
      omega 
    exact h5 
    all_goals linarith