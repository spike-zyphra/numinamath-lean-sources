import Mathlib

theorem algebra_20784 {a c : ℕ} (ha : 0 < a) (hc : 0 < c)
    (hroots : ∀ x : ℕ, 2*x^3-2*a*x^2+(a^2-81)*x-c=0 → x=1 ∨ x=2 ∨ x=3)
    (h : ∃ x : ℕ, 0 < x ∧ 2*x^3-2*a*x^2+(a^2-81)*x-c=0 ∧ x≠1 ∧ x≠2 ∧ x≠3) :
    c=440 := by 
  rcases h with ⟨x, ⟨hx1, hx2, hx3, hx4, hx5⟩⟩ 
  have h1 := hroots x (show 2 * x^3 - 2 * a * x^2 + (a^2 - 81) * x - c = 0 by omega)
  cases h1 with
  | inl h1 =>
    exfalso
    exact hx3 h1
  | inr h2 =>
    cases h2 with
    | inl h2 =>
      exfalso
      exact hx4 h2
    | inr h3 =>
      exfalso
      exact hx5 h3