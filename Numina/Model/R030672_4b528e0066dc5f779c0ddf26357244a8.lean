import Mathlib

theorem number_theory_177240 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) :
    (fun x => x - (Nat.digits 10 x).sum)^[100] n = 0 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₀, h₁⟩
  interval_cases n <;> native_decide