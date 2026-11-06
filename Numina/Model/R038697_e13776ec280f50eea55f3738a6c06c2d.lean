import Mathlib

theorem number_theory_255594 {a b c : ℕ} (h₀ : a.gcd b = 15) (h₁ : a.gcd c = 5)
    (h₂ : b.gcd c = 20) (h₃ : a * b * c = 2^4 * 3^2 * 5^3) :
    a = 15 ∧ b = 60 ∧ c = 20 := by 
  have h4 : 15 ∣ a := by 
    have h41 : a.gcd b ∣ a := by 
      exact Nat.gcd_dvd_left a b 
    rw [show a.gcd b = 15 by exact h₀] at h41 
    exact h41 
  have h5 : 15 ∣ b := by 
    have h51 : a.gcd b ∣ b := by 
      exact Nat.gcd_dvd_right a b 
    rw [show a.gcd b = 15 by exact h₀] at h51 
    exact h51 
  have h6 : 5 ∣ a := by 
    have h61 : a.gcd c ∣ a := by 
      exact Nat.gcd_dvd_left a c 
    rw [show a.gcd c = 5 by exact h₁] at h61 
    exact h61 
  have h7 : 5 ∣ c := by 
    have h71 : a.gcd c ∣ c := by 
      exact Nat.gcd_dvd_right a c 
    rw [show a.gcd c = 5 by exact h₁] at h71 
    exact h71 
  have h8 : 20 ∣ b := by 
    have h81 : b.gcd c ∣ b := by 
      exact Nat.gcd_dvd_left b c 
    rw [show b.gcd c = 20 by exact h₂] at h81 
    exact h81 
  have h9 : 20 ∣ c := by 
    have h91 : b.gcd c ∣ c := by 
      exact Nat.gcd_dvd_right b c 
    rw [show b.gcd c = 20 by exact h₂] at h91 
    exact h91 
  have h10 : 60 ∣ b := by
    have h11 : 15 ∣ b := h5
    have h12 : 20 ∣ b := h8
    have h13 : 60 ∣ b := by
      omega 
    exact h13
  have h13 : a * b * c = 18000 := by
    norm_num at h₃ ⊢ 
    linarith 
  have h14 : ∃ m : ℕ, a = 15 * m := by 
    refine' ⟨a / 15, by 
      omega 
    ⟩
  rcases h14 with ⟨m, hm⟩
  have h15 : ∃ n : ℕ, b = 60 * n := by 
    refine' ⟨b / 60, by 
      omega 
    ⟩
  rcases h15 with ⟨n, hn⟩
  have h16 : ∃ p : ℕ, c = 20 * p := by 
    refine' ⟨c / 20, by 
      omega 
    ⟩
  rcases h16 with ⟨p, hp⟩
  rw [hm, hn, hp] at h13 
  have h17 : m * n * p = 1 := by
    nlinarith
  have hm1 : m = 1 := by 
    have h20 : m ∣ 1 := by 
      use (n * p)
      all_goals nlinarith 
    have h21 : m ≤ 1 := by 
      exact Nat.le_of_dvd (by norm_num) h20
    interval_cases m <;> try { 
      omega 
    }
  have hn1 : n = 1 := by 
    have h22 : n ∣ 1 := by 
      use (m * p)
      all_goals nlinarith 
    have h23 : n ≤ 1 := by 
      exact Nat.le_of_dvd (by norm_num) h22
    interval_cases n <;> try { 
      omega 
    }
  have hp1 : p = 1 := by 
    have h24 : p ∣ 1 := by 
      use (m * n)
      all_goals nlinarith 
    have h25 : p ≤ 1 := by 
      exact Nat.le_of_dvd (by norm_num) h24
    interval_cases p <;> try { 
      omega 
    }
  have ha1 : a = 15 := by
    nlinarith [hm, hm1]
  have hb1 : b = 60 := by
    nlinarith [hn, hn1]
  have hc1 : c = 20 := by
    nlinarith [hp, hp1]
  exact ⟨ha1, hb1, hc1⟩