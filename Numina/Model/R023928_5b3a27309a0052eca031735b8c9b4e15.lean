import Mathlib

theorem algebra_117774 : ¬∃ P : Polynomial ℤ, ∃ a b c : ℤ, a ≠ b ∧ b ≠ c ∧ c ≠ a ∧ P.eval a = b ∧ P.eval b = c ∧ P.eval c = a := by
  rintro ⟨P, ⟨a, b, c, ha, hb, hc, hevala, hevalb, hevalc⟩⟩
  have h1 : (a - b) ∣ (P.eval a - P.eval b) := by
    apply P.sub_dvd_eval_sub
  have h1' : (P.eval a - P.eval b) = (b - c) := by
    rw [hevala, hevalb]
  rw [h1'] at h1
  have h2 : (b - c) ∣ (P.eval b - P.eval c) := by
    apply P.sub_dvd_eval_sub
  have h2' : (P.eval b - P.eval c) = (c - a) := by
    rw [hevalb, hevalc]
  rw [h2'] at h2
  have h3 : (c - a) ∣ (P.eval c - P.eval a) := by
    apply P.sub_dvd_eval_sub
  have h3' : (P.eval c - P.eval a) = (a - b) := by
    rw [hevalc, hevala]
  rw [h3'] at h3
  have h4 : a - b ≠ 0 := by
    intro h
    apply ha
    omega
  have h5 : b - c ≠ 0 := by
    intro h
    apply hb
    omega
  have h6 : c - a ≠ 0 := by
    intro h
    apply hc
    omega
  obtain ⟨k, hk⟩ := h1
  obtain ⟨m, hm⟩ := h2
  obtain ⟨n, hn⟩ := h3
  have hk1 : k * m * n = 1 := by
    have h12 : a - b = n * (c - a) := by linarith
    rw [show c - a = m * (b - c) by linarith [hm]] at h12
    have h13 : a - b = n * (m * (b - c)) := by linarith [h12]
    rw [show b - c = k * (a - b) by linarith [hk]] at h13
    have h14 : a - b = n * m * (k * (a - b)) := by linarith [h13]
    have h15 : (1 : ℤ) = n * m * k := by
      apply (mul_left_inj' (show a - b ≠ 0 by exact h4)).mp
      linarith
    have h16 : k * m * n = 1 := by
      ring_nf at h15 ⊢
      linarith
    linarith
  have h7 : k = 1 ∨ k = -1 := by
    have h8 : k ∣ 1 := by
      use m * n
      all_goals 
        nlinarith
    have h9 : k = 1 ∨ k = -1 := by
      have h10 : k ∣ 1 := h8
      have h11 : k = 1 ∨ k = -1 := by
        have h12 : k ≤ 1 := by 
          apply Int.le_of_dvd (by norm_num) h10
        have h13 : k ≥ -1 := by
          have h14 : -k ∣ 1 := by
            exact Int.neg_dvd.2 h10
          have h15 : -k ≤ 1 := by
            apply Int.le_of_dvd (by norm_num) h14
          omega
        interval_cases k <;> tauto
      tauto
    tauto
  cases h7 with
  | inl hk3 =>
    have hm1 : m * n = 1 := by
      rw [show k = 1 by linarith [hk3]] at hk1
      nlinarith
    have hm2 : m = 1 ∨ m = -1 := by
      have h8 : m ∣ 1 := by
        use n
        all_goals
          nlinarith
      have h9 : m = 1 ∨ m = -1 := by
        have h10 : m ∣ 1 := h8
        have h11 : m = 1 ∨ m = -1 := by
          have h12 : m ≤ 1 := by 
            apply Int.le_of_dvd (by norm_num) h10
          have h13 : m ≥ -1 := by
            have h14 : -m ∣ 1 := by
              exact Int.neg_dvd.2 h10
            have h15 : -m ≤ 1 := by
              apply Int.le_of_dvd (by norm_num) h14
            omega
          interval_cases m <;> tauto
        tauto
      tauto
    cases hm2 with
    | inl hm3 =>
      have hn1 : n = 1 := by
        rw [show m = 1 by linarith [hm3]] at hm1
        nlinarith
      have heq1 : 2 * b = a + c := by
        rw [show k = 1 by linarith [hk3]] at hk
        linarith
      have heq2 : 2 * c = a + b := by
        rw [show m = 1 by linarith [hm3]] at hm
        linarith
      have heq3 : 2 * a = b + c := by
        rw [show n = 1 by linarith [hn1]] at hn
        linarith
      have heq4 : b - c = 0 := by
        nlinarith
      exfalso
      apply h5
      linarith
    | inr hm3 =>
      have hn1 : n = -1 := by
        rw [show m = -1 by linarith [hm3]] at hm1
        nlinarith
      have heq1 : 2 * b = a + c := by
        rw [show k = 1 by linarith [hk3]] at hk
        linarith
      have heq2 : b = a := by
        rw [show m = -1 by linarith [hm3]] at hm
        linarith
      exfalso
      apply ha
      omega
  | inr hk3 =>
    have hm1 : m * n = -1 := by
      rw [show k = -1 by linarith [hk3]] at hk1
      nlinarith
    have hm2 : m = 1 ∨ m = -1 := by
      have h8 : m ∣ 1 := by
        use -n
        all_goals
          nlinarith
      have h9 : m = 1 ∨ m = -1 := by
        have h10 : m ∣ 1 := h8
        have h11 : m = 1 ∨ m = -1 := by
          have h12 : m ≤ 1 := by 
            apply Int.le_of_dvd (by norm_num) h10
          have h13 : m ≥ -1 := by
            have h14 : -m ∣ 1 := by
              exact Int.neg_dvd.2 h10
            have h15 : -m ≤ 1 := by
              apply Int.le_of_dvd (by norm_num) h14
            omega
          interval_cases m <;> tauto
        tauto
      tauto
    cases hm2 with
    | inl hm3 =>
      have hn1 : n = -1 := by
        rw [show m = 1 by linarith [hm3]] at hm1
        nlinarith
      have heq1 : c = a := by
        rw [show k = -1 by linarith [hk3]] at hk
        linarith
      exfalso
      apply hc
      omega
    | inr hm3 =>
      have hn1 : n = 1 := by
        rw [show m = -1 by linarith [hm3]] at hm1
        nlinarith
      have heq1 : c = a := by
        rw [show k = -1 by linarith [hk3]] at hk
        linarith
      exfalso
      apply hc
      omega