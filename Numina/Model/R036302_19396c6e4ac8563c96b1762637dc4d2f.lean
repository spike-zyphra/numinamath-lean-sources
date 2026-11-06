import Mathlib

theorem number_theory_225720 (n : ℕ) (hn : n ≥ 5) (a : Fin n → ℝ)
    (ha : ∀ i j, a i ≠ a j) (h : ∀ i j, ∃ k l, k ≠ i ∧ k ≠ j ∧ l ≠ i ∧ l ≠ j ∧
    a k + a l = a i + a j) :
    n = 13 := by
  exfalso
  have h2 := h (⟨0, by linarith⟩) (⟨0, by linarith⟩)
  rcases h2 with ⟨k, l, hk, hj, hl, hj2, hsum⟩
  have h0 := ha k k
  contradiction
  all_goals try simp_all
  all_goals try { 
    simp [Fin.ext_iff] at ha h2 ⊢
    all_goals try { contradiction }
    all_goals try { simp_all }
    all_goals try { exfalso <;> simp_all } 
  }
  <;> try { 
    simp_all [Fin.ext_iff, Fin.mk.injEq] 
    <;> try { contradiction }
    <;> try { simp_all } 
    <;> try { exfalso <;> simp_all <;> try { contradiction } } 
  }
  all_goals try { 
    tauto <;> simp_all <;> try { tauto } <;> try { simp_all }
    <;> try { tauto <;> simp_all } <;> try { contradiction }
  }
  <;> try { 
    aesop <;> simp_all <;> try { tauto }
    <;> try { simp_all } 
    <;> try { tauto <;> simp_all }
    <;> try { contradiction }
  }