import Mathlib

theorem number_theory_228480 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : (Nat.digits 10 n).length = 3)
    (h₂ : (Nat.digits 10 n).toFinset.card = 3) (h₃ : 7 ∣ n) (h₄ : 7 ∣ (Nat.digits 10 n).sum) :
    n = 518 ∨ n = 581 ∨ n = 329 ∨ n = 392 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₅, h₆⟩
  interval_cases n <;> norm_num at h₃ h₄ h₁ h₂ ⊢
  <;> try { omega }
  <;> try { tauto }
  <;> norm_num at *
  <;> try { contradiction }
  <;> try { trivial }
  <;> try { tauto }
  <;> try { contradiction }
  <;> try { norm_num at h₁ h₂ h₃ h₄ ⊢; }
  <;> try { all_goals contradiction }