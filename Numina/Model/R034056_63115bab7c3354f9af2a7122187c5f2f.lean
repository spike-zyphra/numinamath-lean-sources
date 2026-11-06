import Mathlib

theorem algebra_16543 {ω : ℂ} (hω : ω^3 = 1 ∧ ω ≠ 1) :
    (1 - ω + ω^2)^4 + (1 + ω - ω^2)^4 = -16 := by 
  rcases hω with ⟨h1, h2⟩
  have eq1 : ω ^ 3 = 1 := h1
  have eq2 : ω^2 + ω + 1 = 0 := by
    have eq3 : ω^3 - 1 = 0 := by
      rw [eq1]
      all_goals norm_num
    have eq4 : ω^3 - 1 = (ω - 1) * (ω^2 + ω + 1) := by 
      ring_nf
    rw [eq4] at eq3 
    cases' (mul_eq_zero.mp eq3) with eq5 eq6
    · -- Case where $\omega - 1 = 0$
      have eq4' : ω = 1 := by
        exact_mod_cast eq_of_sub_eq_zero eq5
      tauto 
    · -- Case where $\omega^2 + \omega + 1 = 0$
      exact_mod_cast eq6
  have eq3 : ω ^ 2 = -ω - 1 := by 
    calc 
      ω ^ 2 = ω ^ 2 + ω + 1 - ω - 1 := by ring_nf 
      _ = 0 - ω - 1 := by rw [eq2]
      _ = -ω - 1 := by ring_nf
  have eq6 : (1 - ω + ω ^ 2) ^ 2 = -4 * (ω + 1) := by 
    calc
      (1 - ω + ω ^ 2) ^ 2
        = (1 - ω + (-ω - 1)) ^ 2 := by rw [eq3]
      _ = ( -2 * ω ) ^ 2 := by ring_nf
      _ = 4 * (ω ^ 2) := by ring_nf 
      _ = 4 * (-ω - 1) := by rw [eq3]
      _ = -4 * (ω + 1) := by ring_nf
  have eq7 : (1 - ω + ω ^ 2) ^ 4 = 16 * ω := by
    calc
      (1 - ω + ω ^ 2) ^ 4 
        = ((1 - ω + ω ^ 2) ^ 2) ^ 2 := by ring_nf
      _ = (-4 * (ω + 1)) ^ 2 := by rw [eq6]
      _ = 16 * (ω + 1) ^ 2 := by ring_nf
      _ = 16 * (ω ^ 2 + 2 * ω + 1) := by ring_nf
      _ = 16 * ((-ω - 1) + 2 * ω + 1) := by rw [eq3]
      _ = 16 * ω := by ring_nf
  have eq8 : (1 + ω - ω ^ 2) ^ 2 = 4 * ω := by
    calc
      (1 + ω - ω ^ 2) ^ 2
        = (1 + ω - (-ω - 1)) ^ 2 := by rw [eq3]
      _ = (2 + 2 * ω) ^ 2 := by ring_nf
      _ = 4 * (1 + 2 * ω + ω ^ 2) := by ring_nf
      _ = 4 * (1 + 2 * ω + (-ω - 1)) := by rw [eq3]
      _ = 4 * (ω) := by ring_nf
      _ = 4 * ω := by ring_nf
  have eq9 : (1 + ω - ω ^ 2) ^ 4 = -16 * (ω + 1) := by
    calc
      (1 + ω - ω ^ 2) ^ 4 
        = ((1 + ω - ω ^ 2) ^ 2) ^ 2 := by ring_nf
      _ = (4 * ω) ^ 2 := by rw [eq8]
      _ = 16 * (ω ^ 2) := by ring_nf 
      _ = 16 * (-ω - 1) := by rw [eq3]
      _ = -16 * (ω + 1) := by ring_nf
  calc 
    (1 - ω + ω ^ 2) ^ 4 + (1 + ω - ω ^ 2) ^ 4
      = 16 * ω + (-16 * (ω + 1)) := by rw [eq7, eq9]
    _ = 16 * ω - 16 * ω - 16 := by ring_nf 
    _ = -16 := by ring_nf