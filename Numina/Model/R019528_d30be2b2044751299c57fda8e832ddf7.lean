import Mathlib

theorem number_theory_1321 (n : ℕ) (h₀ : n < 10^2000) (h₁ : (n / 10^1999) % 10 = 3)
    (h₂ : ∀ i, 17 ∣ (n / 10^i) % 100 ∨ 23 ∣ (n / 10^i) % 100) :
    n % 1000000 = 234692 ∨ n % 1000000 = 234685 := by
  have h3 := h₂ 1999
  have h4 : (n / 10^1999) < 10 := by
    have h5 : n < 10^2000 := h₀
    have h6 : n / 10^1999 < 10 := by
      norm_num at h5 ⊢
      omega
    omega
  have h7 : n / 10^1999 = 3 := by
    have h8 : (n / 10^1999) % 10 = 3 := h₁
    have h9 : n / 10^1999 < 10 := h4
    interval_cases k : n / 10^1999 <;> omega
    all_goals omega
  have h10 : (n / 10^1999) % 100 = 3 := by
    rw [h7]
    all_goals omega
  rcases h3 with h3 | h3
  · -- Assume $17 \mid (n / 10^{1999}) \bmod 100$
    have h11 : 17 ∣ (n / 10^1999) % 100 := h3
    rw [h10] at h11
    omega
  · -- Assume $23 \mid (n / 10^{1999}) \bmod 100$
    have h11 : 23 ∣ (n / 10^1999) % 100 := h3
    rw [h10] at h11
    omega