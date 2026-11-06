import Mathlib

theorem number_theory_140620 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) :
    let f (n : ℕ) := n - (Nat.digits 10 n).sum
    f^[100] n = 0 := by
  rw [Finset.mem_Icc] at h₀ 
  rcases h₀ with ⟨h₃, h₄⟩
  interval_cases n <;> native_decide