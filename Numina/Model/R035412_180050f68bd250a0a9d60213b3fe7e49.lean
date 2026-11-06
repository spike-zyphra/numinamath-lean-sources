import Mathlib

theorem number_theory_611167: IsLeast {a: ℕ | ∃ x y z: ℕ,(1 ≤ x) ∧ (x ≤ 9) ∧ (y ≤ 9) ∧ (z ≤ 9) ∧
(a = x * 10^4 + y * 10^3 + z * 10^2 + y * 10 + x) ∧ (99 ∣ a)} 54945 := by
  constructor 
  · -- Show that 54945 is in the set 
    use 5, 4, 9 
    all_goals norm_num 
  · -- Show that any element in the set is >= 54945 
    intro a ha 
    rcases ha with ⟨x, y, z, hx1, hx2, hy2, hz2, ha_eq, hdiv⟩ 
    by_contra h 
    push_neg at h 
    have h1 : x * 10^4 + y * 10^3 + z * 10^2 + y * 10 + x < 54945 := by linarith 
    have h2 : x ≤ 5 := by
      omega 
    have h3 : y ≤ 9 := by
      omega 
    have h4 : z ≤ 9 := by 
      omega 
    interval_cases x <;> interval_cases y <;> omega