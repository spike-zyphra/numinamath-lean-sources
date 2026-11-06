import Mathlib

theorem number_theory_281437 (n : ℕ) (h₀ : n ∈ Finset.Icc 1821 1994) (h₁ : (Nat.digits 10 n).length = 4)
    (h₂ : (Nat.digits 10 n)[0]! + (Nat.digits 10 n)[1]! = 3 * ((Nat.digits 10 n)[2]! + (Nat.digits 10 n)[3]!))
    (h₃ : (Nat.digits 10 n)[1]! > (Nat.digits 10 n)[0]!) :
    n = 1821 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₄, h₅⟩
  interval_cases n <;> norm_num at *
  <;> try { simp_all }