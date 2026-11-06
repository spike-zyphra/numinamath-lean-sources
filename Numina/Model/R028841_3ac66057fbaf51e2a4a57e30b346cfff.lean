import Mathlib

theorem number_theory_99299 (a : ℕ → ℕ) (ha : StrictMono a)
    (h : ∀ n, ∃ d r : ℕ, a n + d = a (n + 1) ∧ a (n + 1) + d = a (n + 2) ∨
      r ≠ 0 ∧ a n * r = a (n + 1) ∧ a (n + 1) * r = a (n + 2)) (h1 : 4 ∣ a 0) (h2 : 4 ∣ a 1) :
    ¬∃ p, Nat.Prime p ∧ ∃ n, a n = p := by 
  intro h3
  rcases h3 with ⟨p, hp, ⟨n, hn⟩⟩
  have h4 : ∀ (n : ℕ), 4 ∣ a n := by 
    intro n 
    induction' n using Nat.strongRecOn with n ih 
    cases n with 
    | zero => 
      exact h1 
    | succ n' => 
      cases n' with 
      | zero => 
        exact h2 
      | succ n' => 
        have h_n := h n' 
        rcases h_n with ⟨d, r, h₁ | h₂⟩
        · 
          have h3 : 4 ∣ a n' := ih (n') (by linarith)
          have h4 : 4 ∣ a (n' + 1) := ih (n' + 1) (by linarith)
          have h5 : 4 ∣ a (n' + 2) := by 
            omega 
          exact h5 
        · 
          have h3 : 4 ∣ a n' := ih (n') (by linarith)
          have h4 : 4 ∣ a (n' + 1) := ih (n' + 1) (by linarith)
          have h5 : 4 ∣ a (n' + 2) := by 
            have hb : a n' * r = a (n' + 1) := h₂.2.1 
            have hc : a (n' + 1) * r = a (n' + 2) := h₂.2.2 
            have h₃ : 4 ∣ a (n' + 1) := h4 
            have h₄ : 4 ∣ (a (n' + 1) * r) := by 
              obtain ⟨k, hk⟩ := h₃ 
              use k * r 
              rw [hk] 
              <;> ring_nf <;> omega 
            have : a (n' + 2) = a (n' + 1) * r := by 
              omega 
            rw [this] 
            tauto 
          exact h5 
  have h5 : 4 ∣ a n := h4 n 
  rw [hn] at h5 
  have h6 : ¬ Nat.Prime p := by 
    have h7 : 4 ∣ p := h5 
    have : p ≥ 2 := Nat.Prime.two_le hp 
    have : ¬ Nat.Prime p := by 
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by 
        omega 
      ) (by omega) 
      all_goals 
        omega 
    assumption 
  contradiction
  all_goals 
  try { omega } 
  all_goals try { tauto }