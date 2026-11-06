import Mathlib

theorem number_theory_34210 {n : ℕ} (h1 : 19250 % n = 11) (h2 : 20302 % n = 3) :
    n = 53 := by
  have h3 : n ≤ 19250 := by
    by_contra h
    push_neg at h
    have h4 : 19250 % n = 19250 := by
      rw [Nat.mod_eq_of_lt]
      all_goals linarith
    omega
  have h4 : n ≤ 20302 := by
    by_contra h
    push_neg at h
    have h5 : 20302 % n = 20302 := by
      rw [Nat.mod_eq_of_lt]
      all_goals linarith
    omega
  have h40 : n ∣ 19239 := by
    have h44 : (19250 : ℕ) % n = 11 := h1
    have h444 : (19250 : ℕ) = n * (19250 / n) + (19250 % n) := by
      rw [Nat.div_add_mod]
    rw [h44] at h444
    have h45 : (19239 : ℕ) = n * (19250 / n) := by
      omega
    rw [h45] 
    exact dvd_mul_right n (19250 / n)
  have h14 : n ∣ 20299 := by
    have h44 : (20302 : ℕ) % n = 3 := h2
    have h444 : (20302 : ℕ) = n * (20302 / n) + (20302 % n) := by
      rw [Nat.div_add_mod]
    rw [h44] at h444
    have h442 : (20299 : ℕ) = n * (20302 / n) := by
      omega 
    rw [h442] 
    exact dvd_mul_right n (20302 / n)
  have h42 : n ∣ 53 := by
    exact Nat.dvd_gcd h40 h14 
  have h43 : n ∣ 53 := h42
  have h44 : n = 1 ∨ n = 53 := by
    have h45 : n ∣ 53 := h43
    have h46 : n ≤ 53 := by 
      exact Nat.le_of_dvd (by linarith) h45
    interval_cases n <;> try tauto
  rcases h44 with (r | r)
  · 
    rw [show n = 1 by omega] at h1
    all_goals norm_num at h1 
  · 
    omega