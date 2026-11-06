import Mathlib

theorem algebra_205850 (a : ℤ) (ha : a ≠ 1) :
    ∃ k : ℤ, (a ^ 2 + a - 1) / (a - 1) = k ↔ a = 0 ∨ a = 2 := by
  by_cases h1 : a - 1 ∣ a ^ 2 + a - 1
  · -- Case where $a - 1$ divides $a^2 + a - 1$
    have h2 : a - 1 ∣ 1 := by
      have h1' : a - 1 ∣ a ^ 2 + a - 1 := h1
      have h3 : a - 1 ∣ (a - 1) * (a + 2) := by
        apply dvd_mul_of_dvd_left
        exact dvd_refl (a - 1)
      have h4 : a - 1 ∣ (a ^ 2 + a - 1 - ( (a - 1) * (a + 2) ) ) := by
        apply Dvd.dvd.sub
        · exact h1'
        · exact h3
      have h5 : a ^ 2 + a - 1 - ( (a - 1) * (a + 2) ) = 1 := by
        ring
      rw [h5] at h4
      exact h4
    have h3 : a - 1 = 1 ∨ a - 1 = -1 := by
      have h4 : a - 1 ∣ 1 := h2
      have h5 : a - 1 ≤ 1 := by
        exact Int.le_of_dvd (by norm_num) h4
      have h6 : a - 1 ≥ -1 := by
        have h7 : (- (a - 1)) ∣ 1 := by
          exact Int.neg_dvd.2 h4
        have h8 : - (a - 1) ≤ 1 := by
          exact Int.le_of_dvd (by norm_num) h7
        omega
      interval_cases (a - 1) <;> tauto
    rcases h3 with h4 | h4
    · -- case a -1 =1, so a=2 
      have ha2 : a = 2 := by 
        omega
      have hk5 : (a ^ 2 + a - 1) / (a - 1) = 5 := by
        rw [ha2]
        all_goals norm_num
      use 5
      simp [hk5]
      all_goals tauto
    · -- case a -1 =-1, so a=0
      have ha0 : a = 0 := by 
        omega
      have hk1 : (a ^ 2 + a - 1) / (a - 1) = 1 := by
        rw [ha0]
        all_goals norm_num
      use 1
      simp [hk1]
      all_goals tauto
  · -- Case where $a - 1$ does not divide $a^2 + a - 1$
    have h1' : ¬ (a - 1 ∣ a ^ 2 + a - 1) := h1
    have h4 : ¬ (a = 0 ∨ a = 2) := by
      by_contra h5
      rcases h5 with (r | r)
      · -- a = 0
        rw [r] at h1'
        norm_num at h1'
      · -- a = 2
        rw [r] at h1'
        norm_num at h1'
    use ( (a ^ 2 + a - 1) / (a - 1) + 1 )
    constructor
    · -- Assume integer division result = k, prove a = 0 ∨ a = 2
      intro h
      have h5 : (a ^ 2 + a - 1) / (a - 1) = (a ^ 2 + a - 1) / (a - 1) + 1 := by linarith [h]
      omega
    · -- Assume a = 0 ∨ a = 2, prove integer division result = k
      intro h5
      tauto