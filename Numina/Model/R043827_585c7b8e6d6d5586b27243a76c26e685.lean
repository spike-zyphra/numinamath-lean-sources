import Mathlib

theorem number_theory_201789 (n : ℕ) (h₀ : n ∈ Finset.Icc 10 99) (h₁ : (Nat.digits 10 n).length = 2)
    (h₂ : (Nat.digits 10 n).toFinset.card = 2) (h₃ : n^2 = (Nat.sum (Nat.digits 10 n))^3) :
    n = 27 := by 
  rw [Finset.mem_Icc] at h₀ 
  rcases h₀ with ⟨h₄, h₅⟩
  interval_cases n <;> norm_num at h₃ h₁ h₂ ⊢ <;> all_goals 
    try { tauto }
    <;> try { contradiction }
    <;> try { native_decide }