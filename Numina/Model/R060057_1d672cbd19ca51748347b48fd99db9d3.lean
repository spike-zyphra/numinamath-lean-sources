import Mathlib

theorem number_theory_205815 (x y z : ℕ) (hx : 1 ≤ x ∧ x ≤ 9) (hy : 0 ≤ y ∧ y ≤ 9)
    (hz : 0 ≤ z ∧ z ≤ 9) (h : (100 * x + 10 * y + z) = Nat.factorial x + Nat.factorial x + Nat.factorial z) :
    x + y + z = 10 := by
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with ⟨hy1, hy2⟩
  rcases hz with ⟨hz1, hz2⟩
  interval_cases x <;> interval_cases y <;> interval_cases z
  <;> try simp [Nat.factorial] at h <;> all_goals omega
  <;> try tauto
  <;> try omega