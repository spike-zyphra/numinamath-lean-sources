import Mathlib

theorem algebra_16035 {n : ℕ} (h₀ : n ∈ Finset.Ioo 50 100) (h₁ : 11 ∣ n) (h₂ : ¬2 ∣ n)
    (h₃ : 3 ∣ (Nat.digits 10 n).sum) : n = 99 := by
  rw [Finset.mem_Ioo] at h₀
  rcases h₀ with ⟨h4, h5⟩
  interval_cases n <;> norm_num at *
  <;> try { tauto }
  <;> native_decide