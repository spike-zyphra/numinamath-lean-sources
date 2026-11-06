import Mathlib

def E : Set ℚ := {x | ∃ m : ℤ, x = m + 1 / 6}
def F : Set ℚ := {x | ∃ n : ℤ, x = n / 2 - 1 / 3}
def G : Set ℚ := {x | ∃ p : ℤ, x = p / 2 + 1 / 6}

theorem algebra_215312 : E ⊂ F ∧ F = G := by 
  constructor
  · -- Show that $E \subsetneq F$
    constructor 
    · -- Show that $E \subseteq F$
      intro x hx
      rcases hx with ⟨m, hm⟩ 
      use 2 * m + 1 
      rw [hm]
      field_simp 
      <;> ring 
    · -- Show that $E \neq F$
      have h1 : ( -1 / 3 : ℚ ) ∈ F := by 
        use 0 
        norm_num 
      have h2 : ( -1 / 3 : ℚ ) ∉ E := by 
        intro h 
        rcases h with ⟨m, hm⟩ 
        have h3 : (m : ℚ) = (-1 / 2 : ℚ) := by 
          linarith 
        have h4 : 2 * (m : ℚ) = (-1 : ℚ) := by 
          linarith 
        have h5 : 2 * m = (-1 : ℤ) := by 
          exact_mod_cast h4 
        omega 
      intro h 
      have h3 : ( -1 / 3 : ℚ ) ∈ E := by 
        have h4 : ( -1 / 3 : ℚ ) ∈ F := h1 
        have h5 : F ⊆ E := by 
          exact h 
        have h6 : ( -1 / 3 : ℚ ) ∈ E := by 
          apply h5 
          exact h4 
        exact h6
      contradiction
  · -- Show that $F = G$
    ext x 
    simp only [F, G, Set.mem_setOf_eq]
    constructor
    · -- Assume x ∈ F, prove x ∈ G
      rintro ⟨n, hn⟩
      use n - 1 
      rw [hn]
      field_simp 
      <;> ring
    · -- Assume x ∈ G, prove x ∈ F 
      rintro ⟨p, hp⟩
      use p + 1
      rw [hp]
      field_simp 
      <;> ring