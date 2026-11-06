import Mathlib

theorem algebra_88526 : IsLeast {w : ℤ | ∃ (x y z : ℤ), 0 < x ∧ 0 < y ∧ 0 < z ∧ x * y + z = 160 ∧ w = x + y * z} 50 := by
  constructor
  · -- Prove that 50 is in the set
    use 26, 6, 4
    all_goals norm_num
  · -- Prove that 50 is the least element in the set
    intro w hw
    rcases hw with ⟨x, y, z, hx, hy, hz, h1, h2⟩
    by_contra h
    push_neg at h
    have h3 : x ≤ 49 := by
      have hy1 : y ≥ 1 := by linarith
      have hz1 : z ≥ 1 := by linarith
      have h7 : y * z ≥ 1 := by nlinarith
      nlinarith
    have h4 : y ≤ 50 := by
      nlinarith
    have h5 : z ≤ 49 := by
      have h6 : x ≥ 1 := by linarith
      have h7 : y ≥ 1 := by linarith
      nlinarith
    interval_cases y <;> try { 
      omega 
    }