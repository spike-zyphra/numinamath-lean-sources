import Mathlib

theorem number_theory_180574 (x y : ℤ) :
    3 * x + 5 * y = 7 ↔ ∃ k : ℤ, (x, y) = (4 + 5 * k, -1 - 3 * k) := by
  constructor
  · -- Assume $3 * x + 5 * y = 7$, we need to prove $\exists k : \mathbb{Z}, (x, y) = (4 + 5 * k, -1 - 3 * k)$.
    intro h
    use (x - 4) / 5
    have h1 : 3 * x + 5 * y = 7 := h
    have h2 : 5 % 3 = 2 := by norm_num
    have h3 : x % 5 = 4 % 5 := by
      omega
    have h4 : 5 ∣ (x - 4) := by 
      omega
    have hx : x = 4 + 5 * ((x - 4) / 5) := by 
      omega
    have hy : y = -1 - 3 * ((x - 4) / 5) := by 
      omega
    have eq1 : (x, y) = (4 + 5 * ((x - 4) / 5), -1 - 3 * ((x - 4) / 5)) := by 
      exact Prod.ext hx hy
    exact eq1
  · -- Assume $\exists k : \mathbb{Z}, (x, y) = (4 + 5 * k, -1 - 3 * k)$, we need to prove $3 * x + 5 * y = 7$.
    rintro ⟨k, h⟩
    rcases h with ⟨rfl, rfl⟩
    ring_nf