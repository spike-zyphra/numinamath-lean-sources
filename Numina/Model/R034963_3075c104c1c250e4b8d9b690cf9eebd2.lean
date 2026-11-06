import Mathlib

theorem number_theory_280344 {f g : ℕ → ℕ}
    (hf : ∀ m n, Nat.Coprime m n → f m * f n = f (m * n))
    (hg : ∀ m n, Nat.Coprime m n → g m * g n = g (m * n)) :
    ∀ m n, Nat.Coprime m n → (f * g) m * (f * g) n = (f * g) (m * n) := by
  intro m n h_coprime
  have h1 : f m * f n = f (m * n) := hf m n h_coprime
  have h2 : g m * g n = g (m * n) := hg m n h_coprime
  simp [Prod.ext_iff] at *
  <;> nlinarith [h1, h2]