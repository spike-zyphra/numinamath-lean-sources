import Mathlib

/-- the vieta formula of quartic equation. -/
lemma vieta_quartic (a b c d x₁ x₂ x₃ x₄ : ℝ) (h_roots : ∀ (x:ℝ), (x - x₁) * (x - x₂) * (x - x₃) * (x - x₄) = x^4 + a * x^3 + b * x^2 + c * x + d) :
  x₁ + x₂ + x₃ + x₄ = -a ∧ x₁ * x₂ + x₁ * x₃ + x₁ * x₄ + x₂ * x₃ + x₂ * x₄ + x₃ * x₄ = b ∧ x₁ * x₂ * x₃ + x₁ * x₂ * x₄ + x₁ * x₃ * x₄ + x₂ * x₃ * x₄ = -c ∧ x₁ * x₂ * x₃ * x₄ = d := by
  have h0:= h_roots 0
  ring_nf at h0
  have h1:= h_roots 1
  ring_nf at h1
  have hm1:= h_roots (-1)
  ring_nf at hm1
  have h2:= h_roots 2
  ring_nf at h2
  constructor
  linarith
  constructor
  linarith
  constructor
  linarith
  assumption

/-- The fourth-degree polynomial $\(x^{4}-18 x^{3}+k x^{2}+200 x-1984\)$ has four roots, and the product of two of these roots is $\(-32\)$. Find the real number $\(k\)$.-/
theorem algebra_4030
  (k : ℝ)
  (h_roots : ∃(x₁ x₂ x₃ x₄:ℝ ),(∀ (x:ℝ), (x - x₁) * (x - x₂) * (x - x₃) * (x - x₄) = x^4 + (-18) * x^3 + k * x^2 + 200 * x - 1984)∧ (x₁ * x₂ = -32)) : k=86 := by
   obtain ⟨x₁,x₂,x₃,x₄, h_eq,hvt⟩ := h_roots
   -- get the relation of roots according to above lemma.
   have h0:= vieta_quartic (-18) k 200 (-1984) x₁ x₂ x₃ x₄ h_eq
   have h4:=h0.2.2.2
   have h34: x₃ * x₄ = 62 := by rw[hvt] at h4;linarith
   have h3:=h0.2.2.1
   rw[hvt,mul_assoc,h34,mul_assoc,h34] at h3
   rw[← h0.2.1]
   nlinarith
