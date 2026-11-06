import Mathlib

theorem number_theory_50323 (S : Set ℤ) (h1 : ∃ x y, x ∈ S ∧ y ∈ S ∧ (x, y) = 1 ∧ (x - 2, y - 2) = 1)
    (h2 : ∀ x y, x ∈ S → y ∈ S → (x ^ 2 - y) ∈ S) :
    S = ⊤ := by 
  rcases h1 with ⟨x, y, hx, hy, hxy, hxy2⟩
  have hx2 : x ^ 2 - y ∈ S := h2 x y hx hy
  have hy2 : y ^ 2 - x ∈ S := h2 y x hy hx
  have h3 : (x ^ 2 - y) ^ 2 - (y ^ 2 - x) ∈ S := h2 (x ^ 2 - y) (y ^ 2 - x) hx2 hy2
  have h4 : (y ^ 2 - x) ^ 2 - (x ^ 2 - y) ∈ S := h2 (y ^ 2 - x) (x ^ 2 - y) hy2 hx2
  
  -- Now we extend the set to include all integers
  ext a
  simp
  <;> aesop