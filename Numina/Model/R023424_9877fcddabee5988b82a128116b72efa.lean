import Mathlib

theorem algebra_7011 {n : ℕ} (hn : 2 ≤ n) (f : Fin n → ℂ) :
    Complex.abs (∏ i : Fin n, f i) = ∏ i : Fin n, Complex.abs (f i) := by
  have h1 : Complex.abs (∏ i : Fin n, f i) = ∏ i : Fin n, Complex.abs (f i) := by
    simp_all [Complex.abs_prod]
    all_goals try tauto
    all_goals try linarith
  exact h1
  <;> try tauto
  <;> try { tauto }
  <;> try { tauto }
  <;> try { tauto }
  all_goals try { tauto }
  all_goals try { tauto }
  all_goals try { tauto }
  all_goals try { try { tauto } }