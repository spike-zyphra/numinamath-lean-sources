import Mathlib

theorem number_theory_237502 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) :
    ¬(∃ a b c, a * b * c = n ∧ a = (n / 100 + 1) ∧ b = (n % 100 / 10 + 1) ∧ c = (n % 10)) := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₁, h₂⟩
  rintro ⟨a, b, c, h_eq1, h_eq2, h_eq3, h_eq4⟩
  interval_cases n <;> norm_num [h_eq2, h_eq3, h_eq4] at h_eq1 <;> all_goals omega