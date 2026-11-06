import Mathlib

theorem number_theory_59458 {n : ℕ} (hn : n = 1000) :
    IsLeast {p | p.Prime ∧ p ∣ n} 2 ∧
    IsGreatest {p | p.Prime ∧ p ∣ n} 11 →
    2 * 11 = 1681 := by
  intro h
  rcases h with ⟨h1, h2⟩
  rw [hn] at h1 h2
  have h11_in : 11 ∈ {p | p.Prime ∧ p ∣ (1000 : ℕ)} := by
    have h11_greatest : IsGreatest {p | p.Prime ∧ p ∣ (1000 : ℕ)} 11 := h2
    exact h11_greatest.left
  have h11_dvd : 11 ∣ (1000 : ℕ) := by 
    have h11_in' : 11 ∈ {p | p.Prime ∧ p ∣ (1000 : ℕ)} := h11_in
    have h11_dvd' : 11 ∣ (1000 : ℕ) := h11_in'.right
    exact h11_dvd'
  norm_num at h11_dvd
  all_goals omega