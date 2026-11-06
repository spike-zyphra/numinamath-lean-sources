import Mathlib

theorem number_theory_4763 :
    IsGreatest {x | ∃ y z : ℕ, x.Prime ∧ y.Prime ∧ z.Prime ∧ x + y + z = 101} 97 := by 
  constructor
  · -- Show that 97 is in the set
    use 2, 2
    all_goals norm_num
  · -- Show that 97 is the greatest in the set
    rintro x ⟨y, z, hx, hy, hz, h_eq⟩
    by_contra h
    push_neg at h
    have h1 : x ≥ 98 := by linarith
    have h2 : y + z ≤ 3 := by linarith
    have h3 : y ≥ 2 := Nat.Prime.two_le hy
    have h4 : z ≥ 2 := Nat.Prime.two_le hz
    have h5 : y + z ≥ 4 := by linarith
    linarith