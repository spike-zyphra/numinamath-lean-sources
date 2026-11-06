import Mathlib

theorem algebra_291600 :
  {(f, s, si) : ℕ × ℕ × ℕ | 
    ∃ u : ℕ, 
      
      f - u = (s - u) + (si - u) ∧
      
      f + 6 = 3 * (s - u) ∧
      
      s = f - u ∧
      
      f + 19 = 2 * si} =
  {(69, 47, 44)} := by
  ext ⟨f, s, si⟩
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First, we will show that if $(f, s, si)$ is in the set, then $(f, s, si) = (69, 47, 44)$.
    rintro ⟨u, h1, h2, h3, h4⟩
    have eq1 : u ≤ f := by
      by_contra h
      push_neg at h
      have h5 : f - u = 0 := by
        omega
      omega
    have eq2 : u ≤ s := by
      by_contra h
      push_neg at h
      have h7 : s - u = 0 := by
        omega
      omega
    have eq3 : u ≤ si := by
      by_contra h
      push_neg at h
      have h8 : si - u = 0 := by
        omega
      omega
    have eq4 : s = f - u := by 
      omega
    have eq5 : f = 69 := by
      omega
    have eq7 : s = 47 := by
      omega
    have eq8 : si = 44 := by
      omega
    simp [eq5, eq7, eq8]
  · -- Now, we will show the converse.
    rintro ⟨rfl, rfl, rfl⟩
    use 22
    all_goals 
      omega