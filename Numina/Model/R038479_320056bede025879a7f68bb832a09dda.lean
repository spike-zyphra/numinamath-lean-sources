import Mathlib

theorem number_theory_289584 (a b c : ℕ) (h₀ : b / a = 3 ∧ b % a = 3) (h₁ : c / a = 9 ∧ c % a = 11) :
    c % b = 2 := by 
  have h2 : a > 0 := by
    by_contra h
    push_neg at h
    have ha0 : a = 0 := by omega
    have hb1 : b / a = 3 := h₀.1
    have hb2 : b % a = 3 := h₀.2
    rw [ha0] at hb1 hb2
    all_goals
      omega

  have eq1 : b = 3 * a + 3 := by
    have h3 : b = a * (b / a) + (b % a) := by
      rw [Nat.div_add_mod b a]
    rw [h₀.1, h₀.2] at h3
    omega

  have eq2 : c = 9 * a + 11 := by
    have h4 : c = a * (c / a) + (c % a) := by
      rw [Nat.div_add_mod c a]
    rw [h₁.1, h₁.2] at h4
    omega

  rw [eq1] 
  rw [eq2]

  have h6 : (9 * a + 11) % (3 * a + 3) = 2 := by
    have eq3 : (9 * a + 11) = 3 * (3 * a + 3) + 2 := by
      ring_nf
    rw [eq3]
    simp [Nat.add_mod, Nat.mul_mod]

  exact h6