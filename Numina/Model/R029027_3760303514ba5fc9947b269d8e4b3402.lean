import Mathlib

theorem number_theory_4887_1 (f g : ℕ → ℕ)
    (hmf : ∀ m n, Nat.Coprime m n → f m * f n = f (m * n))
    (hmg : ∀ m n, Nat.Coprime m n →  g m * g n = g (m * n)) :
    ∀ m n, Nat.Coprime m n → (f * g) m * (f * g) n = (f * g) (m * n) := by
  --we prove that if f and g are multiplicative functions, then fg is also multiplicative
  --unwinding the assumptions then simplify
  intro m n hmn; simp
  have r1 := hmf m n hmn
  have r2 := hmg m n hmn
  rw [← r1, ← r2]; ring

theorem number_theory_4887_2 (f g : ℕ → ℕ)
    (hmf : ∀ m n, f m * f n = f (m * n))
    (hmg : ∀ m n, g m * g n = g (m * n)) :
    ∀ m n, (f * g) m * (f * g) n = (f * g) (m * n) := by
  --we prove that if f and g are completely multiplicative functions, then fg is also completely multiplicative
  intro m n; simp
  have r1 := hmf m n
  have r2 := hmg m n
  rw [← r1, ← r2]; ring