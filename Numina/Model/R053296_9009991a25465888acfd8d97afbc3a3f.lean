import Mathlib

def A : Set ℤ := {x | 1 ≤ x ∧ x ≤ 9}
def B : Set (ℤ × ℤ) := {p | p.1 ∈ A ∧ p.2 ∈ A}
def f : ℤ × ℤ → ℤ := fun (a, b) => a * b - a - b

theorem algebra_12829 :
    {p ∈ B | f p = 11}.encard = 4 := by
  have h1 : {p ∈ B | f p = 11} = {(3, 7), (4, 5), (5, 4), (7, 3)} := by
    ext ⟨a, b⟩
    simp [B, A, f]
    constructor
    · -- Assume (a, b) ∈ {p ∈ B | f p = 11}, then (a, b) ∈ B and f (a, b) = 11
      rintro ⟨⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩, h⟩
      have h1 : a ≥ 1 := by linarith
      have h2 : a ≤ 9 := by linarith
      have h3 : b ≥ 1 := by linarith
      have h4 : b ≤ 9 := by linarith
      interval_cases a <;> interval_cases b <;> omega
    · -- Assume (a, b) ∈ {(3, 7), (4, 5), (5, 4), (7, 3)}, then (a, b) ∈ B and f (a, b) = 11
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      all_goals
        simp
        <;> tauto
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_eq_toFinset_card']
  <;> try { rfl }
  all_goals try { linarith }