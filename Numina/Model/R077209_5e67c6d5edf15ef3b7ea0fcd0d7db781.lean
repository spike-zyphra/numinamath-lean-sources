import Mathlib

theorem number_theory_216888 :
    {(b, m) : ℕ × ℕ | b * 42 + m * 25 = 1511}.encard = 2 := by
  have h1 : {(b, m) : ℕ × ℕ | b * 42 + m * 25 = 1511} = { (33, 5), (8, 47) } := by
    ext ⟨b, m⟩
    simp
    constructor
    · -- Assume (b, m) is a solution, prove (b, m) in { (33, 5), (8, 47) }
      rintro H
      have h2 : b ≤ 36 := by
        omega
      have h3 : m ≤ 60 := by
        omega
      interval_cases b <;> omega
    · -- Assume (b, m) in { (33, 5), (8, 47) }, then (b, m) is a solution
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · norm_num
      · norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_pair]
  <;> try { done }
  <;> try { linarith }
  <;> try { native_decide }