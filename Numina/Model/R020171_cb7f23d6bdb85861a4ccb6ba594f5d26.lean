import Mathlib

theorem algebra_95929 (a b c : ℤ) (ha : a ≠ b) (hb : b ≠ c) (hc : a ≠ c)
    (P : Polynomial ℤ) (hP : P.eval a = b) (hP' : P.eval b = c) (hP'' : P.eval c = a) :
    False := by 
  have h1 : a - b ≠ 0 := by 
    intro h
    apply ha
    linarith
  have h2 : b - c ≠ 0 := by 
    intro h
    apply hb
    linarith
  have h3 : c - a ≠ 0 := by 
    intro h
    apply hc
    linarith
  have h10 : (a - b) ∣ (P.eval a - P.eval b) := by 
    apply Polynomial.sub_dvd_eval_sub
  have h11 : (b - c) ∣ (P.eval b - P.eval c) := by 
    apply Polynomial.sub_dvd_eval_sub
  have h12 : (c - a) ∣ (P.eval c - P.eval a) := by 
    apply Polynomial.sub_dvd_eval_sub
  rw [hP, hP'] at h10
  rw [hP', hP''] at h11
  rw [hP'', hP] at h12
  --Since $a - b | b - c$, then exists integer $k$ s.t. $b - c = k(a - b)$.
  obtain ⟨k, hk⟩ := h10
  obtain ⟨m, hm⟩ := h11
  obtain ⟨n, hn⟩ := h12
  have h_eq1 : b - c = k * (a - b) := by 
    linarith
  have h_eq2 : c - a = m * (b - c) := by
    linarith
  have h_eq3 : a - b = n * (c - a) := by
    linarith 
  have h_eq4 : a - b = n * m * k * (a - b) := by 
    rw [show c - a = m * (b - c) by linarith [h_eq2]] at h_eq3 
    rw [show b - c = k * (a - b) by linarith [h_eq1]] at h_eq3 
    nlinarith 
  have h_eq5 : (a - b) * (1 - n * m * k) = 0 := by 
    nlinarith 
  -- Since $\ a \neq b$, so $a-b \neq 0$, we have $1 - n * m * k = 0 $ implies $n * m * k = 1$.
  have h_eq6 : n * m * k = 1 := by 
    apply_fun (λ x => x / (a - b)) at h_eq5 
    field_simp [show a - b ≠ 0 by exact h1] at h_eq5 
    linarith 
  have hk1 : k ∣ 1 := by 
    use m * n 
    nlinarith 
  have hm1 : m ∣ 1 := by 
    use k * n 
    nlinarith 
  have hn1 : n ∣ 1 := by 
    use k * m 
    nlinarith 
  have hk2 : k = 1 ∨ k = -1 := by 
    have : k ≤ 1 := by 
      apply Int.le_of_dvd (by norm_num) hk1
    have : k ≥ -1 := by 
      have h1 : -k ∣ 1 := by 
        exact Int.neg_dvd.2 hk1
      have h2 : -k ≤ 1 := by 
        apply Int.le_of_dvd (by norm_num) h1
      linarith 
    interval_cases k <;> tauto 
  have hm2 : m = 1 ∨ m = -1 := by 
    have : m ≤ 1 := by 
      apply Int.le_of_dvd (by norm_num) hm1 
    have : m ≥ -1 := by 
      have h1 : -m ∣ 1 := by 
        exact Int.neg_dvd.2 hm1 
      have h2 : -m ≤ 1 := by 
        apply Int.le_of_dvd (by norm_num) h1 
      linarith 
    interval_cases m <;> tauto 
  have hn2 : n = 1 ∨ n = -1 := by 
    have : n ≤ 1 := by 
      apply Int.le_of_dvd (by norm_num) hn1 
    have : n ≥ -1 := by 
      have h1 : -n ∣ 1 := by 
        exact Int.neg_dvd.2 hn1 
      have h2 : -n ≤ 1 := by 
        apply Int.le_of_dvd (by norm_num) h1 
      linarith 
    interval_cases n <;> tauto 
  rcases hk2 with hk2 | hk2 
  · -- Let's assume $k=1$
    have hk2' : m * n = 1 := by 
      rw [hk2] at h_eq6 
      nlinarith 
    rcases hm2 with hm2 | hm2 
    · -- Assume $m=1$
      have hn2' : n = 1 := by 
        rw [hm2] at hk2' 
        nlinarith 
      have h_eq5a : a - b = 0 := by 
        nlinarith [show b - c = k * (a - b) by linarith [h_eq1], show c - a = m * (b - c) by linarith [h_eq2], show a - b = n * (c - a) by linarith [h_eq3]] 
      exfalso 
      exact ha (by linarith) 
    · -- Assume $m=-1$
      have hn2' : n = -1 := by 
        rw [hm2] at hk2' 
        nlinarith 
      have h_eq5a : a - b = 0 := by 
        nlinarith [show b - c = k * (a - b) by linarith [h_eq1], show c - a = m * (b - c) by linarith [h_eq2], show a - b = n * (c - a) by linarith [h_eq3]] 
      exfalso 
      exact ha (by linarith) 
  · -- Let's assume $k=-1$
    have hk2' : m * n = -1 := by 
      rw [hk2] at h_eq6 
      nlinarith 
    rcases hm2 with hm2 | hm2 
    · -- Assume $m=1$
      have hn2' : n = -1 := by 
        rw [hm2] at hk2' 
        nlinarith 
      have h_eq5a : a - b = 0 := by 
        nlinarith [show b - c = k * (a - b) by linarith [h_eq1], show c - a = m * (b - c) by linarith [h_eq2], show a - b = n * (c - a) by linarith [h_eq3]] 
      exfalso 
      exact ha (by linarith) 
    · -- Assume $m=-1$
      have hn2' : n = 1 := by 
        rw [hm2] at hk2' 
        nlinarith 
      have h_eq5a : a - b = 0 := by 
        nlinarith [show b - c = k * (a - b) by linarith [h_eq1], show c - a = m * (b - c) by linarith [h_eq2], show a - b = n * (c - a) by linarith [h_eq3]] 
      exfalso 
      exact ha (by linarith)
  all_goals linarith