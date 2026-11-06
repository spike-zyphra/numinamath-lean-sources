import Mathlib

theorem number_theory_213133 (n : ℕ) (a : Fin n → ℤ) (h : ∑ i : Fin n, a i = 1996) :
    ∑ i : Fin n, (a i)^3 ≡ 4 [ZMOD 6] := by
  have h1 : ∀ x : ℤ, x^3 % 6 = x % 6 := by
    intro x
    have h1 : x % 6 = 0 ∨ x % 6 = 1 ∨ x % 6 = 2 ∨ x % 6 = 3 ∨ x % 6 = 4 ∨ x % 6 = 5 := by
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1) <;> simp [h1, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
  have h2 : ∀ i : Fin n, (a i)^3 % 6 = a i % 6 := by
    intro i
    apply h1 
  have h3 : (∑ i : Fin n, (a i)^3) % 6 = (∑ i : Fin n, a i) % 6 := by
    simp [Finset.sum_int_mod, h2]
  have h4 : (∑ i : Fin n, a i) % 6 = 4 := by
    rw [h]
    omega 
  show ∑ i : Fin n, (a i)^3 ≡ 4 [ZMOD 6]
  rw [Int.modEq_iff_dvd]
  omega