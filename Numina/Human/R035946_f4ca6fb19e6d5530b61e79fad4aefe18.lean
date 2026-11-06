import Mathlib

theorem number_theory_168335 {n : ℕ} (h₀ : n ∈ Finset.Icc 10 99) (h₁ : 5 ∣ n) (h₂ : ¬3 ∣ n) (h₃ : ¬4 ∣ n)
(h₄ : Even (97 * n)) (h₅ : 6 ≤ n / 10) : n = 70 := by
  have h6 : n ≥ 10 := Finset.mem_Icc.mp h₀ |>.1
  have h7 : n ≤ 99 := Finset.mem_Icc.mp h₀ |>.2
  interval_cases n <;> norm_num at *
  <;> tauto