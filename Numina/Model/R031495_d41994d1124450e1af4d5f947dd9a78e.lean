import Mathlib

theorem algebra_177522_explicit :
    let S : Set ℝ := { z | ∃ x y : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ x + y ≤ 100 ∧ x / 200 + y / 40 ≤ 1 ∧ z = 20 * x + 60 * y };
    (∃ x y : ℝ, x = 75 ∧ y = 25 ∧ 
     x ≥ 0 ∧ y ≥ 0 ∧ x + y ≤ 100 ∧ x / 200 + y / 40 ≤ 1) ∧
    (20 * 75 + 60 * 25) ∈ S ∧
    (∀ z ∈ S, z ≤ 20 * 75 + 60 * 25) := by
  constructor
  · -- First part: show that (75, 25) is a feasible solution.
    use 75, 25
    all_goals norm_num
  constructor
  · -- Second part: show that the total value is in the set
    use 75, 25
    norm_num
  · -- Third part: prove maximality
    intro z hz
    rcases hz with ⟨x, y, hx, hy, h1, h2, hz⟩
    nlinarith