import Mathlib

theorem algebra_303157 {k p : ℕ} (hk : 0 < k) (hroots : ∃ m n, m > 0 ∧ n > 0 ∧ (k-1)*m^2-p*m+k=0 ∧ (k-1)*n^2-p*n+k=0) :
    k^(p*k) * (p^p + k^k) + (p + k) = 1989 := by
  rcases hroots with ⟨m, n, hm, hn, h1, h2⟩
  have h3 : k - 1 ∣ k := by
    have eq1' : (k - 1) * m^2 + k = p * m := by
      omega
    have h6 : k - 1 ∣ p * m - k := by
      use m^2
      all_goals
        omega
    have h7 : k - 1 ∣ k := by
      have h8 : k - 1 ∣ p * m := by
        have h9 : k - 1 ∣ p * m - k := h6
        have h10 : k - 1 ∣ k := by
          omega
        have h11 : k - 1 ∣ (p * m - k) + k := by
          apply Nat.dvd_add
          · exact h9
          · exact h10
        have h12 : (p * m - k) + k = p * m := by
          omega
        rw [h12] at h11
        exact h11
      have h10 : k - 1 ∣ k := by
        omega
      omega
    exact h7
  have h4 : k - 1 = 1 := by
    have h5 : k - 1 ∣ k := h3
    have h8 : k - 1 ∣ 1 := by
      have h9 : k - 1 ∣ k := h5
      have h10 : k - 1 ∣ k - 1 := by
        use 1
        all_goals
          omega
      have h11 : k - 1 ∣ (k - (k - 1)) := by
        apply Nat.dvd_sub'
        · -- Show that k - 1 divides k
          exact h9
        · -- Show that k - 1 divides k - 1
          exact h10
      have h12 : k - (k - 1) = 1 := by
        omega
      rw [h12] at h11
      exact h11
    have h11 : k - 1 ≤ 1 := by
      exact Nat.le_of_dvd (by norm_num) h8
    have h12 : k - 1 ≥ 1 := by
      have hk1 : k > 0 := hk
      by_cases h : k > 1
      · -- k > 1
        omega
      · -- k ≤ 1
        have h13 : k = 1 := by
          omega
        omega
    have h13 : k - 1 = 1 := by
      omega
    exact h13
  have h4' : k = 2 := by
    omega
  have h5 : p * m - k = m^2 := by
    rw [show k = 2 by omega] at h1
    omega
  have h6 : p * n - k = n^2 := by
    rw [show k = 2 by omega] at h2
    omega
  have h7 : m * n = 2 := by
    nlinarith [h1, h2, h4', h5, h6]
  have h8 : m ∣ 2 := by
    use n
    linarith [h7]
  have h9 : n ∣ 2 := by
    use m
    linarith [h7]
  have h10 : m = 1 ∨ m = 2 := by
    have h11 : m ≤ 2 := by
      have h12 : m ∣ 2 := h8
      exact Nat.le_of_dvd (by norm_num) h12
    interval_cases m <;> omega
  rcases h10 with (h11 | h11)
  · -- m = 1
    have h12 : n = 2 := by
      rw [h11] at h7
      linarith
    have h13 : p = 3 := by
      rw [h11] at h5
      omega
    rw [h4', h13]
    all_goals
      norm_num
  · -- m = 2
    have h12 : n = 1 := by
      rw [h11] at h7
      linarith
    have h13 : p = 3 := by
      rw [h11] at h5
      omega
    rw [h4', h13]
    all_goals
      norm_num