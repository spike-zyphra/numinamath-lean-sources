import Mathlib

theorem number_theory_273695 (a : ℕ → ℕ) (h₀ : ∀ n, a n = a 0 + 30 * n) :
    {n | 0 ≤ n ∧ n < 7 ∧ 7 ∣ a n}.encard = 1 := by 
  have h2 : {n | 0 ≤ n ∧ n < 7 ∧ 7 ∣ a n} = { (3 * (a 0 % 7)) % 7 } := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · -- First, show that if n is in the left side, equals to the right.
      rintro ⟨hn0, hn7, hdiv⟩
      have h3 : n < 7 := hn7
      have h4 : a n = a 0 + 30 * n := h₀ n 
      have h5 : (a n) % 7 = 0 := by 
        omega
      rw [h4] at h5
      have h6 : (a 0 + 30 * n) % 7 = 0 := h5
      have h7 : n < 7 := hn7 
      have h8 : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by omega 
      rcases h8 with (r | r | r | r | r | r | r) <;> 
        simp [r] at h6 h5 h4 hdiv ⊢ 
        <;> 
          omega
    · -- Show that the right side element is in the left side.
      intro hn 
      have h8 : n = (3 * (a 0 % 7)) % 7 := by omega 
      have hn0 : 0 ≤ n := by omega 
      have hn7 : n < 7 := by omega 
      constructor 
      · exact hn0 
      constructor 
      · exact hn7 
      · -- Show that 7 ∣ a n.
        have h8 : a n = a 0 + 30 * n := h₀ n 
        have h_mod : (a n) % 7 = 0 := by 
          rw [h8]
          have h9 : n = (3 * (a 0 % 7)) % 7 := by omega 
          have h13 : (a 0 + 30 * n) % 7 = 0 := by 
            have h9 : n = (3 * (a 0 % 7)) % 7 := by omega
            rw [h9]
            have h14 : (30 : ℕ) % 7 = 2 := by norm_num
            simp [Nat.add_mod, h14] at *
            <;> 
              omega 
          omega 
        omega 
  rw [h2]
  simp [Set.encard_singleton]