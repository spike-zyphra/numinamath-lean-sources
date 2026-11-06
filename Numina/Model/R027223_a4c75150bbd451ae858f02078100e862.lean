import Mathlib

theorem number_theory_69156 :
    Set.Infinite {(x, y, z) : ℕ × ℕ × ℕ | x ^ 2 + y ^ 2 + z ^ 2 - x * y - y * z - z * x = 3} := by
  apply Set.infinite_of_injective_forall_mem (f := λ (n : ℕ) => (n + 2, n + 1, n))
  · -- Show the map is injective
    intro n m h
    simp [Prod.ext_iff] at h
    all_goals omega
  · -- Show all elements in the image are in the set
    intro n
    simp [Prod.ext_iff]
    all_goals
      ring_nf
      <;> omega