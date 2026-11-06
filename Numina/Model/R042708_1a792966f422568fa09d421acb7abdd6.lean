import Mathlib

theorem number_theory_8363 :
    Set.Infinite {l : ℤ × ℤ | l.1 ≠ 0 ∧ (10 : ℝ) * l.2 = l.1 * (1 / 2)} := by
  have h1 : {l : ℤ × ℤ | l.1 ≠ 0 ∧ (10 : ℝ) * l.2 = l.1 * (1 / 2)} = {l : ℤ × ℤ | l.1 ≠ 0 ∧ (l.1 : ℝ) = 20 * (l.2 : ℝ)} := by
    ext ⟨a, b⟩
    simp only [Set.mem_setOf_eq]
    constructor
    · -- First, show the forward direction
      rintro ⟨ha1, heq⟩
      constructor
      · exact_mod_cast ha1
      · -- Show the equation
        have h3 : (a : ℝ) = 20 * (b : ℝ) := by
          have eq1 : (10 : ℝ) * (b : ℝ) = (a : ℝ) * (1 / 2 : ℝ) := by
            linarith
          nlinarith 
        exact_mod_cast h3
    · -- Show the reverse direction
      rintro ⟨ha1, heq⟩
      constructor
      · exact_mod_cast ha1
      · -- Show the equation
        have h3 : (a : ℝ) = 20 * (b : ℝ) := by
          exact_mod_cast heq
        have h4 : (10 : ℝ) * (b : ℝ) = (a : ℝ) * (1 / 2 : ℝ) := by
          linarith 
        linarith 
  rw [h1]
  apply Set.infinite_of_injective_forall_mem (f := λ (n : ℕ) => (20 * (n + 1 : ℤ), (n + 1 : ℤ)))
  · -- Show f is injective
    intro n m h
    simp [Prod.ext_iff] at h 
    all_goals omega
  · -- Show all elements from f are in the set
    intro n 
    simp [Prod.ext_iff]
    all_goals norm_num
    all_goals ring_nf <;> norm_num
    all_goals try { native_decide }
    all_goals try { tauto }
    all_goals try { native_decide }
    all_goals try { omega }