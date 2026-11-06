import Mathlib

open Polynomial

/- 1. (1996 28th Canadian Mathematical Olympiad) If $\alpha, \beta, \gamma$ are the roots of the equation $x^{3}-x-1=0$, find the value of $\frac{1+\alpha}{1-\alpha}+\frac{1+\beta}{1-\beta}+\frac{1+\gamma}{1-\gamma}$. -/
theorem algebra_133641 {α β γ : ℂ} (hr : (X ^ 3 - X - 1 : Polynomial ℂ).roots = {α, β, γ}) :
    (1 + α) / (1 - α) + (1 + β) / (1 - β) + (1 + γ) / (1 - γ) = -7 := by
  -- use Vieta's identities to show that
  -- α + β + γ = 0, α * β + α * γ + β * γ = -1, and α * β * γ = 1
  have ⟨eq1, eq2, eq3⟩ : α + β + γ = 0 ∧ α * β + α * γ + β * γ = -1 ∧ α * β * γ = 1 := by
    -- it is convenient to construct a Cubic polynomial and
    -- use Cubic.eq_sum_three_roots to get all required identities
    let p3 : Cubic ℂ := { a := 1, b := 0, c := -1, d := -1 }
    have p3_eq : p3.toPoly = X ^ 3 - X - 1 := by
      simp only [Cubic.toPoly, map_one, one_mul, map_zero, zero_mul, add_zero, map_neg, neg_mul]
      ring
    have hroots : (Cubic.map (RingHom.id ℂ) p3).roots = {α, β, γ} := by simp [Cubic.map_roots, p3_eq, hr]
    have eqs := Cubic.eq_sum_three_roots (by norm_num) hroots
    simp only [Cubic.map, RingHom.id_apply, neg_add_rev, one_mul, mul_neg, Cubic.mk.injEq, neg_inj,
      true_and] at eqs
    constructorm* _ ∧ _
    · linear_combination eqs.1
    · rw [eqs.2.1]
    · rw [eqs.2.2]
  -- if x is a root of X ^ 3 - X - 1 then 1 - x ≠ 0 (since 1 is not a root of this polynomial)
  have h0 (x : ℂ) (hx : x ∈ ({α, β, γ} : Multiset ℂ)) : 1 - x ≠ 0 := by
    rw [←hr] at hx
    simp at hx
    contrapose! hx
    intro _
    rw [show x = 1 by linear_combination -hx]
    norm_num
  have ha := h0 α (by simp)
  have hb := h0 β (by simp)
  have hc := h0 γ (by simp)
  -- simplify the expression
  field_simp
  -- use the polyrith tactic to discover that the simplified
  -- expression is a linear combination of Vieta's identities
  linear_combination -(8 * eq1) + 6 * eq2 - 4 * eq3