import Mathlib

theorem algebra_1309 : {x : ℕ | ∃ a b c : ℕ, x = c - a ∧ a + b + c = 30 ∧ 10*a+15*b+20*c=500} = {10} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume x ∈ {x : ℕ | ∃ a b c : ℕ, x = c - a ∧ a + b + c = 30 ∧ 10*a+15*b+20*c=500}, prove x ∈ {10}
    rintro ⟨a, b, c, hx, h1, h2⟩
    have h3 : c ≥ a := by
      omega
    omega
  · -- Assume x ∈ {10}, prove x ∈ {x : ℕ | ∃ a b c : ℕ, x = c - a ∧ a + b + c = 30 ∧ 10*a+15*b+20*c=500}
    intro hx
    rw [hx]
    exact ⟨0, 20, 10, by omega, by omega, by omega⟩