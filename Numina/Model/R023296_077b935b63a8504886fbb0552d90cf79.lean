import Mathlib


lemma lemma_1 {k : ℤ} (hk : k ≠ 1) (h : k - 1 ∣ k ^ 2) :
    k - 1 ∣ 1 := by
  have eq1 : k ^ 2 = (k - 1) * (k + 1) + 1 := by
    ring_nf
  have h2 : k - 1 ∣ (k - 1) * (k + 1) := by
    use k + 1
  have h3 : k - 1 ∣ k ^ 2 - ((k - 1) * (k + 1)) := by
    apply Dvd.dvd.sub
    .
      exact h
    .
      exact h2
  have h4 : k ^ 2 - ((k - 1) * (k + 1)) = 1 := by
    rw [eq1]
    ring
  rw [h4] at h3
  exact h3


theorem algebra_173093 :
    Set.ncard {a : ℕ | 0 < a ∧ ∃ x : ℤ, x^2 - a * x + a = 0} = 1 := by 
  have h1 : {a : ℕ | 0 < a ∧ ∃ x : ℤ, x^2 - a * x + a = 0} = {4} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · -- First, show that if a is in the set, then a = 4
      intro h
      rcases h with ⟨ha_pos, x, hx⟩
      have eq1 : (x : ℤ) ^ 2 = a * (x - 1 : ℤ) := by
        nlinarith
      have h2 : (x - 1 : ℤ) ∣ (x ^ 2 : ℤ) := by
        use a
        linarith [eq1]
      have h3 : (x - 1 : ℤ) ∣ (1 : ℤ) := by
        have hx10 : (x - 1 : ℤ) ≠ 0 := by
          by_contra h0
          have : x - 1 = 0 := by linarith
          have hx1 : x = 1 := by linarith
          rw [hx1] at eq1
          omega
        -- have hx01 : (x - 1 : ℤ) ∣ (1 : ℤ) := by
        have h4 : (x - 1 : ℤ) ∣ (x ^ 2 : ℤ) := h2
        have eq2 : (x ^ 2 : ℤ) = (x - 1) * (x + 1) + 1 := by
          nlinarith
        have h5 : (x - 1 : ℤ) ∣ ((x - 1) * (x + 1) : ℤ) := by
          use x + 1
        have h6 : (x - 1 : ℤ) ∣ ((x ^ 2 : ℤ) - ((x - 1) * (x + 1) : ℤ)) := by
          apply Dvd.dvd.sub
          .
            exact h4
          .
            exact h5
        have eq3 : (x ^ 2 : ℤ) - ((x - 1) * (x + 1) : ℤ) = 1 := by
          nlinarith
        rw [eq3] at h6
        exact h6
      have hx2 : (x - 1 : ℤ) = 1 ∨ (x - 1 : ℤ) = -1 := by
        have h3' : (x - 1 : ℤ) ∣ (1 : ℤ) := h3
        have hx4 : (x - 1 : ℤ) ≤ 1 := by
          apply Int.le_of_dvd (by norm_num) h3'
        have hx5 : (x - 1 : ℤ) ≥ -1 := by
          have hx6 : (- (x - 1 : ℤ)) ∣ (1 : ℤ) := by
            exact Int.neg_dvd.2 h3'
          have hx7 : - (x - 1 : ℤ) ≤ 1 := by
            apply Int.le_of_dvd (by norm_num) hx6
          omega
        interval_cases (x - 1 : ℤ) <;> tauto
      rcases hx2 with h7 | h7
      · -- x - 1 = 1, so x = 2
        have hx2' : x = 2 := by
          omega
        rw [hx2'] at eq1
        have ha1 : (a : ℤ) = 4 := by
          nlinarith
        have ha1' : a = 4 := by
          omega
        tauto
      · -- x - 1 = -1, so x = 0
        have hx0' : x = 0 := by
          omega
        rw [hx0'] at eq1
        have ha0 : (a : ℤ) = 0 := by
          nlinarith
        have ha0' : a = 0 := by
          omega
        omega
    · -- Now show the reverse: 4 is in the set
      intro ha
      rw [ha]
      constructor
      · -- 0 < (4 : ℕ)
        norm_num
      · -- ∃ x : ℤ, x ^ 2 - 4 * x + 4 = 0
        use 2
        all_goals
          norm_num
  rw [h1]
  simp