import Mathlib

theorem algebra_147632 {a b c : ℤ} (ha : ∃ m, a = m^2) (hb : ∃ n, b = n^2)
    (hc : ∃ p, c = p^2) (h1 : a - b = 24) (h2 : b - c = 24) :
    a = 49 ∧ b = 25 ∧ c = 1 := by
  rcases ha with ⟨m, rfl⟩
  rcases hb with ⟨n, rfl⟩
  rcases hc with ⟨p, rfl⟩
  have h_eq1 : m^2 = n^2 + 24 := by linarith
  have h_eq2 : n^2 = p^2 + 24 := by linarith
  have h3 : (m^2 - n^2 : ℤ) = 24 := by linarith
  have h4 : (n^2 - p^2 : ℤ) = 24 := by linarith
  have h5 : (m - n) * (m + n) = 24 := by
    nlinarith
  have h6 : (n - p) * (n + p) = 24 := by
    nlinarith
  have h7 : (n - p) * (n + p) = 24 := by
    nlinarith
  have h8 : (n - p) ∣ 24 := by
    use (n + p)
    all_goals
    linarith [h7]
  have h9 : (n - p) ≤ 24 := by
    exact Int.le_of_dvd (show 0 < 24 by norm_num) h8
  have h10 : (n - p) ≥ -24 := by
    have h10 : -(n - p) ∣ 24 := by
      exact Int.neg_dvd.2 h8
    have h11 : -(n - p) ≤ 24 := by
      exact Int.le_of_dvd (show 0 < 24 by norm_num) h10
    omega
  interval_cases h : (n - p) <;> try { 
    omega 
  } <;> try { 
    have h10 : n ≤ 24 := by nlinarith
    have h11 : n ≥ -24 := by nlinarith
    interval_cases n <;> try { 
      omega 
    } <;> try { 
      have h20 : m ≤ 24 := by nlinarith
      have h21 : m ≥ -24 := by nlinarith
      interval_cases m <;> omega
    }
  }