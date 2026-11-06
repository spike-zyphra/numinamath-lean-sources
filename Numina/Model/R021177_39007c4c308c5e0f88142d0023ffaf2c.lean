import Mathlib

theorem algebra_11093 {a b c : ℤ} (ha : a ≠ 0) (h1 : Even (a + b)) (h2 : Odd c) :
    ¬∃ x : ℤ, a * x ^ 2 + b * x + c = 0 := by
  rintro ⟨x, hx⟩
  have h3 : c = - (a * x ^ 2 + b * x) := by linarith
  have h4 : (a + b) % 2 = 0 := by
    obtain ⟨k, hk⟩ := h1
    omega
  have h5 : (a * x ^ 2 + b * x) % 2 = 0 := by
    have h6 : x % 2 = 0 ∨ x % 2 = 1 := by omega
    rcases h6 with (h6 | h6)
    · -- Case in which x % 2 = 0
      simp [h6, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
      all_goals
        omega
    · -- Case in which x % 2 = 1
      simp [h6, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
      all_goals
        omega
  have h7 : c % 2 = 1 := by
    obtain ⟨k, hk⟩ := h2
    omega
  have h8 : c % 2 = 0 := by
    have eq1 : c = - (a * x ^ 2 + b * x) := h3
    have h_eq2 : (a * x ^ 2 + b * x) % 2 = 0 := h5
    have eq3 : (c : ℤ) % 2 = 0 := by 
      rw [eq1]
      have h_eq3 : (- (a * x ^ 2 + b * x) ) % 2 = 0 := by
        have h_eq4 : (a * x ^ 2 + b * x) % 2 = 0 := h_eq2
        omega
      omega
    exact eq3
  omega