import Mathlib

theorem number_theory_106645 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : 3 = (n / 100)) (h₂ : n.divisors.card = 3) :
    n = 361 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₃, h₄⟩
  have h5 : n ≥ 300 := by 
    omega
  have h6 : n ≤ 399 := by 
    omega
  interval_cases n <;> try { tauto }
  <;> try { contradiction }
  <;> try { native_decide }