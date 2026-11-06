import Mathlib

theorem algebra_314359 {m n : ℕ} (hm : m > 0) (hn : n > 0)
    (h : m * n + 9 * m + 11 * n + 145 = k * (m + 11)) (hk : k > 0)
    (h' : m * n + 9 * m + 11 * n + 145 = k * (9 + n)) :
    k = 25 ∨ k = 47 := by

  have eq1 : k * (m + 11) = k * (9 + n) := by 
    linarith

  have eq2 : m + 11 = 9 + n := by
    apply (mul_left_inj' (show k ≠ 0 by omega)).mp
    linarith

  have eq3 : n = m + 2 := by 
    omega

  rw [eq3] at h h'

  have eq4 : m ^ 2 + 22 * m + 167 = k * (m + 11) := by
    nlinarith

  have h2 : (m + 11) ∣ (m ^ 2 + 22 * m + 167) := by
    use k
    all_goals linarith

  have h3 : (m + 11) ∣ (46 : ℕ) := by
    have h4 : (m + 11) ∣ (m ^ 2 + 22 * m + 167) := h2
    have h6 : (m + 11) ∣ ( (m + 11 ) * (m + 11) ) := by 
      use (m + 11)
      all_goals ring

    have h7 : (m + 11) ∣ ((m ^ 2 + 22 * m + 167) - ( (m + 11 ) * (m + 11) )) := by
      apply Nat.dvd_sub'
      · exact h4 
      · exact h6

    have h8 : ( (m ^ 2 + 22 * m + 167) - ( (m + 11 ) * (m + 11) ) ) = 46 := by 
      ring_nf 
      <;> omega

    rw [h8] at h7
    exact h7

  have h5 : (m + 11) = 23 ∨ (m + 11) = 46 := by
    have h6 : (m + 11) ∣ 46 := h3 
    have h7 : (m + 11) ≥ 12 := by 
      omega

    have h8 : (m + 11) ≤ 46 := by
      exact Nat.le_of_dvd (by norm_num) h6

    interval_cases h9 : (m + 11) <;> norm_num at h6 <;> omega

  cases h5 with
  | inl h11 =>
    have hm12 : m = 12 := by
      omega

    have hk25 : k = 25 := by
      rw [hm12] at eq4 
      omega 

    left
    exact hk25

  | inr h11 =>
    have hm35 : m = 35 := by 
      omega

    have hk47 : k = 47 := by 
      rw [hm35] at eq4 
      omega

    right 
    exact hk47