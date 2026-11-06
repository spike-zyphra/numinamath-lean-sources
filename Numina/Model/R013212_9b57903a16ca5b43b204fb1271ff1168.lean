import Mathlib

theorem number_theory_88693 : Set.ncard {p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 2 = 26 * p.1} ≥ 12 := by 
  have h1 : {p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 2 = 26 * p.1} = 
    {(26, 0), (0, 0), (13, 13), (13, -13), (18, 12), (18, -12), (8, 12), (8, -12), 
     (25, 5), (25, -5), (1, 5), (1, -5)} := by 
    ext ⟨a, b⟩ 
    simp
    constructor 
    · -- Assume $a^2 + b^2 = 26a$, we need to prove $(a,b)$ is one of the listed pairs.
      rintro h 
      have h2 : (a - 13 : ℤ) ^ 2 + (b : ℤ) ^ 2 = 169 := by 
        nlinarith 
      have h3 : (a - 13 : ℤ) ≤ 13 := by nlinarith [sq_nonneg (a - 13 : ℤ), sq_nonneg (b : ℤ)]
      have h4 : (a - 13 : ℤ) ≥ -13 := by nlinarith [sq_nonneg (a - 13 : ℤ), sq_nonneg (b : ℤ)]
      have h3a : a ≤ 26 := by omega 
      have h4a : a ≥ 0 := by omega 
      have h5 : b ≤ 13 := by 
        nlinarith [sq_nonneg (a - 13 : ℤ), sq_nonneg (b : ℤ)]
      have h6 : b ≥ -13 := by 
        nlinarith [sq_nonneg (a - 13 : ℤ), sq_nonneg (b : ℤ)]
      interval_cases a <;> try { 
        interval_cases b <;> norm_num at h2 ⊢ <;> tauto 
      }
    · -- Show that if $(a,b)$ is one of the listed pairs, it satisfies $a^2 + b^2 = 26a$.
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | 
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      all_goals 
        norm_num 
  rw [h1] 
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }