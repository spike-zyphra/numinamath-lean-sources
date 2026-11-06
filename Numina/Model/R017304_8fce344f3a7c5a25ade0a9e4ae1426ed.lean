import Mathlib

theorem number_theory_262226 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : (Nat.digits 10 n).length = 3)
    (h₂ : (Nat.digits 10 n).toFinset.card = 3) (h₃ : ∀ d ∈ (Nat.digits 10 n), d ≠ 0)
    (h₄ : n % ((Nat.ofDigits 10 (List.take 2 (Nat.digits 10 n))) + (Nat.ofDigits 10 (List.take 2 (Nat.digits 10 n) ++ [Nat.digits 10 n].headI)) +
      (Nat.ofDigits 10 (List.take 2 (Nat.digits 10 n) ++ [Nat.digits 10 n].tail.headI))) = 0) :
    n = 138 ∨ n = 294 ∨ n = 351 ∨ n = 459 := by 
  norm_num [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₅, h₆⟩
  have h₇ : n ≤ 999 := h₆
  have h₈ : n ≥ 100 := h₅
  interval_cases n <;> norm_num [Nat.ofDigits] at h₄ h₁ h₂ h₃ ⊢
  <;> norm_num [Finset.mem_Icc] at *
  <;> norm_num at h₄ h₁ h₂ h₃ 
  <;> try { tauto }
  <;> norm_num at * 
  <;> try { tauto <;> try native_decide }
  <;> try omega