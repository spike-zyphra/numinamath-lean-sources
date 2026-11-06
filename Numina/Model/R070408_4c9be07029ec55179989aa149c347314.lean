import Mathlib

theorem algebra_9517 : IsGreatest {z | ∃ x y : ℤ, 0 < x ∧ 0 < y ∧ 40*x+15*y=580 ∧ z=x*y} 140 := by
  constructor
  · -- First part: show that 140 is achievable with x=7, y=20
    use 7, 20
    all_goals norm_num
  · -- Second part: show that no element greater than 140 is in the set
    rintro z hz
    rcases hz with ⟨x, y, hx, hy, heq, heqz⟩
    by_contra h
    push_neg at h
    have h1 : x * y > 140 := by
      nlinarith [heqz]
    -- We need to prove contradiction if x*y > 140 with 40*x + 15*y=580
    have h7 : x ≥ 1 := by nlinarith
    have h8 : y ≥ 1 := by nlinarith
    have h9 : x ≤ 14 := by
      nlinarith
    have h10 : y ≤ 38 := by
      nlinarith
    interval_cases x <;> interval_cases y
    <;> omega