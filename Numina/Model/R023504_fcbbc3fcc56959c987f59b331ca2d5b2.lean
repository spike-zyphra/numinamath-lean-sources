import Mathlib

theorem number_theory_51447 (m n : ℤ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h : m + n - 1 ∣ m ^ 2 + n ^ 2 - 1) :
    ¬Prime (m + n - 1) := by
  intro h2
  have h11 : (m + n - 1) ∣ (m + n - 1) * (m + n + 1) := by 
    use (m + n + 1)
    all_goals ring_nf <;> omega
  have h12 : (m + n - 1) ∣ ((m + n - 1) * (m + n + 1) - (m ^ 2 + n ^ 2 - 1)) := by
    apply Dvd.dvd.sub 
    · exact h11 
    · exact h 
  have h13 : ((m + n - 1) * (m + n + 1) - (m ^ 2 + n ^ 2 - 1)) = 2 * m * n := by
    ring_nf
  have h6 : (m + n - 1) ∣ 2 * m * n := by
    rw [h13] at h12 
    exact h12
  have h4 : (m + n - 1) ∣ 2 ∨ (m + n - 1) ∣ (m * n) := by
    have h4 : (m + n - 1) ∣ 2 * m * n := by
      rw [h13] at h12 
      exact h12
    have h5 : (m + n - 1) ∣ 2 ∨ (m + n - 1) ∣ (m * n) := by
      apply (Prime.dvd_mul h2).mp
      have h7 : (m + n - 1) ∣ 2 * (m * n) := by
        ring_nf at h4 ⊢
        exact h4
      exact h7
    exact h5
  have h10 : (m + n - 1) ∣ m ∨ (m + n - 1) ∣ n := by 
    have h4_copy : (m + n - 1) ∣ 2 ∨ (m + n - 1) ∣ (m * n) := h4
    cases h4_copy with
    | inl h4_left => 
      exfalso
      have h5 : m + n - 1 ≤ 2 := by 
        apply Int.le_of_dvd (by nlinarith) h4_left
      have h6 : m + n - 1 ≥ 3 := by 
        nlinarith
      omega
    | inr h4_right => 
      have h8 : (m + n - 1) ∣ m ∨ (m + n - 1) ∣ n := by 
        apply (Prime.dvd_mul h2).mp
        exact h4_right
      exact h8
  have h20 : (m + n - 1 ∣ 2) ∨ (m + n - 1 ∣ m) ∨ (m + n - 1 ∣ n) := by
    rcases h4 with (h4_left | h4_right)
    · -- Case where it divides 2
      left 
      exact h4_left
    · -- Case where it divides m * n
      rcases h10 with (h10_left | h10_right)
      · -- Case where it divides m
        right 
        left 
        exact h10_left
      · -- Case where it divides n
        right 
        right 
        exact h10_right
  rcases h20 with h21 | h22 | h23
  · -- Assume that m + n - 1 divides 2
    have h3 : (m + n - 1) ≤ 2 := by 
      apply Int.le_of_dvd (by norm_num) h21
    have h5 : m + n - 1 ≥ 3 := by
      linarith
    omega
  · -- Assume that m + n - 1 divides m
    have h6 : m + n - 1 ≤ m := by
      apply Int.le_of_dvd (show 0 < m by linarith) h22
    have h7 : m + n - 1 > m := by 
      omega
    linarith
  · -- Assume that m + n - 1 divides n
    have h8 : m + n - 1 ≤ n := by
      apply Int.le_of_dvd (show 0 < n by linarith) h23
    have h9 : m + n - 1 > n := by
      omega
    linarith