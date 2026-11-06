import Mathlib

theorem number_theory_227483 : ∃ (d m s : ℕ) (h₀ : d ∈ Finset.Icc 10000 99999) (h₁ : m ∈ Finset.Icc 10000 99999)
    (h₂ : s ∈ Finset.Icc 10000 99999) (h₃ : (Nat.digits 10 d).Perm (Nat.digits 10 m)) (h₄ : (Nat.digits 10 m).Perm (Nat.digits 10 s))
    (h₅ : (Nat.digits 10 s).Perm (Nat.digits 10 d)),
    s + m = 2 * d := by 
  use 11111, 11111, 11111
  simp
  <;> native_decide