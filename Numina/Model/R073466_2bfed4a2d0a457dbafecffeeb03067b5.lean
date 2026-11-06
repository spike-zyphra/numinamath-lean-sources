import Mathlib

theorem algebra_120147 (a b : Fin 50 → ℚ) (ha : ∀ i, a i ≠ 0)
    (hb : ∀ i, b i ≠ 0) (h : ∀ i j, a i * b j ≠ 0)
    (h1 : ∀ i, ∃! j, a i = j) (h2 : ∀ i, ∃! j, b i = j)
    (h3 : ∀ i, ¬∃ q : ℚ, a i = q) (h4 : ∀ i, ¬∃ q : ℚ, b i = q) :
    {p | ∃ i j, p = a i * b j ∧ ¬∃ q : ℚ, p = q}.encard ≤ 1250 := by 
  have h5 := h3 0
  have h6 : ∃ q : ℚ, a 0 = q := by 
    refine' ⟨a 0, rfl⟩ 
  cases h6 with 
  | intro q hq =>
    exfalso 
    apply h5 
    exact ⟨q, hq⟩