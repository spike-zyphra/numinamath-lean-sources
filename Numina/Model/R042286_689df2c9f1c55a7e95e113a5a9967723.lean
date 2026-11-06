import Mathlib

open Real

theorem inequalities_157540 (n : ℕ) (hn : 2 ≤ n) :
    logb n (n + 1) > logb (n + 1) (n + 2) := by
  have h1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < (n : ℕ) by omega)
  have h2 : 1 < ((n + 1) : ℝ) := by exact_mod_cast (show 1 < (n + 1 : ℕ) by omega)
  have h3 : logb (n : ℝ) (n + 1) = log (n + 1) / log (n : ℝ) := by
    field_simp [logb]
  have h4 : logb ((n + 1 : ℝ) ) (n + 2) = log (n + 2) / log ((n + 1 : ℝ) ) := by
    field_simp [logb]
  rw [h3, h4]
  have h5 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < (n : ℕ) by omega)
  have h6 : 0 < ((n + 1) : ℝ) := by exact_mod_cast (show 0 < (n + 1 : ℕ) by omega)
  have h7 : 0 < ((n + 2) : ℝ) := by exact_mod_cast (show 0 < (n + 2 : ℕ) by omega)
  have h8 : log (n : ℝ) < log ((n + 1 : ℝ) ) := by
    apply Real.log_lt_log
    linarith
    linarith
  have h9 : log ((n + 1 : ℝ) ) < log ((n + 2 : ℝ) ) := by
    apply Real.log_lt_log
    linarith
    linarith
  have h10 : 0 < log (n : ℝ) := by
    have hn' : (n : ℝ) > 1 := by exact_mod_cast (show 1 < n by omega)
    have : log (n : ℝ) > 0 := by
      apply Real.log_pos
      linarith
    linarith
  have h11 : 0 < log ((n + 1 : ℝ) ) := by
    have hn' : (n + 1 : ℝ) > 1 := by exact_mod_cast (show 1 < n + 1 by omega)
    have : log ((n + 1 : ℝ) ) > 0 := by
      apply Real.log_pos
      linarith
    linarith
  have h12 : 0 < log ((n + 2 : ℝ) ) := by
    have hn' : (n + 2 : ℝ) > 1 := by exact_mod_cast (show 1 < n + 2 by omega)
    have : log ((n + 2 : ℝ) ) > 0 := by
      apply Real.log_pos
      linarith
    linarith
  have h13 : (log ((n + 1 : ℝ) ) ) ^ 2 > log (n : ℝ) * log ((n + 2 : ℝ) ) := by
    have h14 : log ((n + 1 : ℝ) ) - log (n : ℝ) > log ((n + 2 : ℝ) ) - log ((n + 1 : ℝ) ) := by
      have h15 : log ((n + 1 : ℝ) / (n : ℝ) ) = log ((n + 1 : ℝ) ) - log (n : ℝ) := by
        rw [Real.log_div (by linarith) (by linarith)]
      have h16 : log ((n + 2 : ℝ) / ((n + 1 : ℝ) ) ) = log ((n + 2 : ℝ) ) - log ((n + 1 : ℝ) ) := by
        rw [Real.log_div (by linarith) (by linarith)]
      have h17 : (n + 1 : ℝ) / (n : ℝ) > (n + 2 : ℝ) / ((n + 1 : ℝ) ) := by
        have h5' : (n : ℝ) ≥ 2 := by exact_mod_cast (show (2 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn)
        have h6' : (n + 1 : ℝ) ≥ 3 := by linarith
        have h8' : (n + 1 : ℝ) / (n : ℝ) - ((n + 2 : ℝ) / ((n + 1 : ℝ) ) ) > 0 := by
          have h18 : (n + 1 : ℝ) / (n : ℝ) - ((n + 2 : ℝ) / ((n + 1 : ℝ) ) ) = ((n + 1 : ℝ) ^ 2 - (n : ℝ) * (n + 2 : ℝ) ) / ((n : ℝ) * ((n + 1 : ℝ) ) ) := by
            field_simp
            <;> ring
          rw [h18]
          have h19 : (n + 1 : ℝ) ^ 2 - (n : ℝ) * (n + 2 : ℝ) > 0 := by
            nlinarith
          have h20 : (n : ℝ) * ((n + 1 : ℝ) ) > 0 := by
            nlinarith
          exact div_pos h19 h20
        nlinarith
      have h18 : log ((n + 1 : ℝ) / (n : ℝ) ) > log ((n + 2 : ℝ) / ((n + 1 : ℝ) ) ) := by
        apply Real.log_lt_log
        all_goals
          try { positivity } <;> try { nlinarith }
      linarith [h18, h15, h16]
    nlinarith
  apply (div_lt_div_iff (by positivity) (by positivity)).mpr
  nlinarith