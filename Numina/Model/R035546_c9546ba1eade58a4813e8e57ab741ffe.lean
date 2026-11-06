import Mathlib

theorem number_theory_288652 {x : ℤ} (hx : ∃ n, x + 15 = n^2) (hy : ∃ m, x - 74 = m^2) :
    x = 2010 := by
  rcases hx with ⟨n, hn⟩
  rcases hy with ⟨m, hm⟩
  have h1 : n^2 - m^2 = 89 := by
    nlinarith
  have h2 : (n - m) * (n + m) = 89 := by
    linarith [h1]
  have h4 : (n - m) ∣ 89 := by 
    use (n + m)
    all_goals linarith
  have h5 : (n - m) = 1 ∨ (n - m) = -1 ∨ (n - m) = 89 ∨ (n - m) = -89 := by
    have h9 : (n - m) ∣ 89 := h4
    have h6 : (n - m) ≤ 89 := by 
      apply Int.le_of_dvd (by norm_num) h9
    have h7 : (n - m) ≥ -89 := by 
      have h8 : (- (n - m)) ∣ 89 := by 
        exact Int.neg_dvd.2 h9
      have h9 : - (n - m) ≤ 89 := by 
        apply Int.le_of_dvd (by norm_num) h8
      omega
    interval_cases (n - m) <;> tauto
  rcases h5 with (h | h | h | h)
  · -- Case n - m = 1
    have h6 : (n + m) = 89 := by
      rw [h] at h2
      linarith
    have hn45 : n = 45 := by
      nlinarith
    have hx2010 : x = 2010 := by
      nlinarith [hn, hn45]
    assumption
  · -- Case n - m = -1
    have h6 : (n + m) = -89 := by
      rw [h] at h2
      linarith
    have hn45 : n = -45 := by
      nlinarith
    have hx2010 : x = 2010 := by
      nlinarith [hn, hn45]
    assumption
  · -- Case n - m = 89
    have h6 : (n + m) = 1 := by
      rw [h] at h2
      linarith
    have hn45 : n = 45 := by
      nlinarith
    have hx2010 : x = 2010 := by
      nlinarith [hn, hn45]
    assumption
  · -- Case n - m = -89
    have h6 : (n + m) = -1 := by
      rw [h] at h2
      linarith
    have hn45 : n = -45 := by
      nlinarith
    have hx2010 : x = 2010 := by
      nlinarith [hn, hn45]
    assumption