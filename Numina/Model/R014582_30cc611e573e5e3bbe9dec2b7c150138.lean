import Mathlib

theorem algebra_603354 {a b c : ℤ} (ha : a ≠ b) (hb : b ≠ c) (hc : a ≠ c)
    (P : Polynomial ℤ) (hP1 : P.eval a = b) (hP2 : P.eval b = c) (hP3 : P.eval c = a) :
    False := by

  have h1 : (a - b : ℤ) ∣ (P.eval a - P.eval b) := by
    apply Polynomial.sub_dvd_eval_sub
  rw [hP1, hP2] at h1 
  have h2 : (b - c : ℤ) ∣ (P.eval b - P.eval c) := by 
    apply Polynomial.sub_dvd_eval_sub
  rw [hP2, hP3] at h2
  have h3 : (c - a : ℤ) ∣ (P.eval c - P.eval a) := by 
    apply Polynomial.sub_dvd_eval_sub
  rw [hP3, hP1] at h3
  have h4 : a - b ≠ 0 := by
    intro h
    apply ha
    linarith 
  have h5 : b - c ≠ 0 := by
    intro h
    apply hb
    linarith 
  have h6 : c - a ≠ 0 := by
    intro h
    have : a = c := by linarith 
    contradiction 
  obtain ⟨k, hk⟩ := h1
  obtain ⟨m, hm⟩ := h2
  obtain ⟨n, hn⟩ := h3 
  have eq6 : (a - b : ℤ) = (n * m * k) * (a - b) := by 
    have h7 : (a - b : ℤ) = n * (c - a) := by linarith 
    rw [show (c - a : ℤ) = m * (b - c) by linarith] at h7 
    rw [show (b - c : ℤ) = k * (a - b) by linarith] at h7 
    linarith 
  -- Now let's prove $k \cdot m \cdot n = 1$ from $a-b = n*m*k*(a-b)$.
  have h7 : k * m * n = 1 := by
    apply (mul_left_inj' (show (a - b : ℤ) ≠ 0 by omega)).mp
    linarith [eq6]
  -- Now let's get all possible integer solutions of `k*m*n=1`.
  have h14 : k ∣ 1 := by
    use m * n 
    linarith 
  have h15 : m ∣ 1 := by 
    use k * n 
    linarith 
  have h16 : n ∣ 1 := by 
    use k * m 
    linarith 
  have hk1 : k = 1 ∨ k = -1 := by 
    have h : k ∣ 1 := by 
      exact h14 
    have : k = 1 ∨ k = -1 := by
      have h9 : k ≤ 1 := by
        apply Int.le_of_dvd (show (0 : ℤ) < (1 : ℤ) by norm_num) h 
      have h99 : -1 ≤ k := by 
        have h22 : k ∣ 1 := h 
        have h33 : -k ∣ 1 := by 
          exact Int.neg_dvd.2 h22 
        have h44 : -k ≤ 1 := by
          apply Int.le_of_dvd (show (0 : ℤ) < (1 : ℤ) by norm_num) h33 
        omega 
      interval_cases k <;> tauto 
    assumption 
  have hm1 : m = 1 ∨ m = -1 := by 
    have h : m ∣ 1 := by 
      exact h15 
    have : m = 1 ∨ m = -1 := by
      have h9 : m ≤ 1 := by 
        apply Int.le_of_dvd (show (0 : ℤ) < (1 : ℤ) by norm_num) h 
      have h99 : -1 ≤ m := by 
        have h22 : m ∣ 1 := h 
        have h33 : -m ∣ 1 := by 
          exact Int.neg_dvd.2 h22 
        have h44 : -m ≤ 1 := by 
          apply Int.le_of_dvd (show (0 : ℤ) < (1 : ℤ) by norm_num) h33 
        omega 
      interval_cases m <;> tauto 
    assumption 
  have hn1 : n = 1 ∨ n = -1 := by 
    have h : n ∣ 1 := by 
      exact h16 
    have : n = 1 ∨ n = -1 := by 
      have h9 : n ≤ 1 := by 
        apply Int.le_of_dvd (show (0 : ℤ) < (1 : ℤ) by norm_num) h 
      have h99 : -1 ≤ n := by 
        have h22 : n ∣ 1 := h 
        have h33 : -n ∣ 1 := by 
          exact Int.neg_dvd.2 h22 
        have h44 : -n ≤ 1 := by 
          apply Int.le_of_dvd (show (0 : ℤ) < (1 : ℤ) by norm_num) h33 
        omega 
      interval_cases n <;> tauto 
    assumption 
  rcases hk1 with (rfl | rfl) <;> rcases hm1 with (rfl | rfl) <;> rcases hn1 with (rfl | rfl) <;> 
    omega