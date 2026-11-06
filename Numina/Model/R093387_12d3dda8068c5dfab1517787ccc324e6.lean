import Mathlib

theorem algebra_211841 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : (n / 10) % 10 = 9)
    (h₂ : 6 ∣ (Nat.digits 10 n).sum) (h₃ : (100 * (n % 10) + 10 * ((n / 10) % 10) + (n / 100)) =
    2 * n - 99) :
    n = 396 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₄, h₅⟩
  interval_cases n <;> norm_num at h₁ h₂ h₃ <;> omega