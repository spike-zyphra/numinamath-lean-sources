import Mathlib

theorem number_theory_4946 :
    {(p1, p2) : ℕ × ℕ | p1 < 26 ∧ p2 < 26 ∧
      (4 * p1 + 5 * p2) % 26 = p1 ∧
      (3 * p1 + p2) % 26 = p2}.ncard = 1 := by
  have h1 : {(p1, p2) : ℕ × ℕ | p1 < 26 ∧ p2 < 26 ∧
    (4 * p1 + 5 * p2) % 26 = p1 ∧
    (3 * p1 + p2) % 26 = p2} = { (0, 0) } := by
    ext ⟨p1, p2⟩
    simp
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      have hp1 : p1 = 0 := by 
        omega
      have hp2 : p2 = 0 := by
        rw [hp1] at h3 
        omega
      exact ⟨hp1, hp2⟩
    · rintro ⟨rfl, rfl⟩
      constructor
      · norm_num 
      constructor
      · norm_num 
      constructor
      · norm_num 
      · norm_num 
  rw [h1]
  simp [Set.ncard_singleton]