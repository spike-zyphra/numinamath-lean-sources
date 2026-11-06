import Mathlib

theorem number_theory_250507 : {n : ℕ | ∃ a b c d, (1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9 ∧ 1 ≤ c ∧ c ≤ 9 ∧ d ≤ 9 ∧ n = (a * 1000 + b * 100 + c * 10 + d) ∧ ((a * 10 + b) * (c * 10 + d) ∣ n))} = {1734, 1352} := by
  have : {n : ℕ | ∃ a b c d, (1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9 ∧ 1 ≤ c ∧ c ≤ 9 ∧ d ≤ 9 ∧ n = (a * 1000 + b * 100 + c * 10 + d) ∧ ((a * 10 + b) * (c * 10 + d) ∣ n))} = {n : ℕ | 1000 ≤ n ∧ n ≤ 9999 ∧ 1 ≤ n / 10 % 10 ∧ (((n / 1000) * 10 + (n / 100 % 10)) * ((n / 10 % 10) * 10 + (n % 10)) ∣ n)} := by
    ext n
    constructor <;> simp
    · intro a ha₁ ha₂ b hb₁ c hc₁ hc₂ d hd₁ hn₁ hn₂
      use (by omega)
      use (by omega)
      use (by omega)
      rw [show n / 1000 = a by omega]
      rw [show n / 100 % 10 = b by omega]
      rw [show n / 10 % 10 = c by omega]
      rw [show n % 10 = d by omega]
      exact hn₂
    · intro hn₁ hn₂ hn₃ hn₄
      use n / 1000, by omega, by omega
      use n / 100 % 10, by omega
      use n / 10 % 10, by omega, by omega
      use n % 10, by omega, by omega
  rw [this]
  have : {n : ℕ | 1000 ≤ n ∧ n ≤ 9999 ∧ 1 ≤ n / 10 % 10 ∧ (((n / 1000) * 10 + (n / 100 % 10)) * ((n / 10 % 10) * 10 + (n % 10)) ∣ n)} = Finset.filter (λn ↦ 1 ≤ n / 10 % 10 ∧ (((n / 1000) * 10 + (n / 100 % 10)) * ((n / 10 % 10) * 10 + (n % 10)) ∣ n)) (Finset.Icc 1000 9999) := by
    ext n; simp
    tauto
  rw [this]
  suffices Finset.filter (λn ↦ 1 ≤ n / 10 % 10 ∧ (((n / 1000) * 10 + (n / 100 % 10)) * ((n / 10 % 10) * 10 + (n % 10)) ∣ n)) (Finset.Icc 1000 9999) = {1734, 1352} by
    rw [this]
    simp
  native_decide
