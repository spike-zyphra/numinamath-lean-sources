import Mathlib

theorem algebra_134742 :
    {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ x * y + 5 * (x + y) = 2005}.ncard = 10 := by
  have h1 : {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ x * y + 5 * (x + y) = 2005} = Finset.filter (fun p : ℕ × ℕ => p.1 > 0 ∧ p.2 > 0 ∧ p.1 * p.2 + 5 * (p.1 + p.2) = 2005) (Finset.Icc (0 : ℕ) 401 ×ˢ Finset.Icc (0 : ℕ) 401) := by
    ext ⟨x, y⟩
    simp
    intro hx hy heq
    have h2 : x ≤ 401 := by
      nlinarith [show y > 0 by omega, heq]
    have h3 : y ≤ 401 := by
      nlinarith [show x > 0 by omega, heq]
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide