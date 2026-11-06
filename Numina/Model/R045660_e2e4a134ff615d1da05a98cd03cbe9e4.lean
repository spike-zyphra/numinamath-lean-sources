import Mathlib

theorem number_theory_73259 (a : ℕ → ℕ)
    (h₀ : a 0 = 1)
    (h₁ : a 1 = 24)
    (h₂ : ∀ n, a (n + 1) = sInf {m | 0 < m ∧ ¬(∃ k, a k = m) ∧ ¬(Nat.Coprime m (a n))}) :
    ∀ n, 0 < n → ∃ m, a m = n := by
  have h3 := h₂ 0
  have eq1 : a 1 = sInf {m | 0 < m ∧ ¬(∃ k, a k = m) ∧ ¬(Nat.Coprime m (a 0))} := h3
  have eq2 : sInf {m | 0 < m ∧ ¬(∃ k, a k = m) ∧ ¬(Nat.Coprime m (a 0))} = 0 := by
    rw [show a 0 = 1 by linarith [h₀]]
    have h4 : {m | 0 < m ∧ ¬(∃ k, a k = m) ∧ ¬(Nat.Coprime m 1)} = ∅ := by
      ext m
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      have h5 : ¬(Nat.Coprime m 1) := h.2.2
      have h6 : Nat.Coprime m 1 := by
        simp [Nat.Coprime]
      contradiction
    rw [h4]
    simp
  have eq3 : a 1 = 0 := by 
    rw [eq1, eq2]
  have h4 : a 1 = 24 := h₁
  linarith [eq3, h4]