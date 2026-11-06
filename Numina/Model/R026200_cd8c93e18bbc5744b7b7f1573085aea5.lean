import Mathlib

theorem algebra_174119 (m : ℝ) (M N : Set (ℝ × ℝ))
    (hM : M = {(x, y) | y^2 = x - 1}) (hN : N = {(x, y) | y = 2 * x - 2 * m^2 + m - 2}) :
    (M ∩ N).encard = 1 ∨ (M ∩ N).encard = 2 := by
  have h1 : M ∩ N = { (m^2 + 1, m), ( (4 * m^2 - 4 * m + 5)/4 , -m + 1/2 ) } := by
    ext ⟨x, y⟩
    simp [hM, hN]
    constructor
    · -- Suppose (x, y) ∈ M ∩ N
      rintro ⟨h_eq1, h_eq2⟩
      have h_eq3 : (x - (m^2 + 1)) * (x - ((4 * m^2 - 4 * m + 5)/4 )) = 0 := by
        have h_sub : y = 2 * x - 2 * m^2 + m - 2 := by linarith
        rw [h_sub] at h_eq1
        nlinarith [sq_nonneg (2 * x - 2 * m^2 + m - 2), sq_nonneg (x -1), sq_nonneg ((2 * m) - 1) ]
      cases' (mul_eq_zero.mp h_eq3) with h_eq4 h_eq5
      · -- Case 1
        have hx1 : x = m^2 + 1 := by linarith
        have hy1 : y = m := by
          rw [hx1] at h_eq2
          nlinarith
        simp [hx1, hy1]
      · -- Case 2
        have hx2 : x = (4 * m^2 - 4 * m + 5)/4 := by linarith
        have hy2 : y = -m + 1/2 := by
          rw [hx2] at h_eq2
          nlinarith
        simp [hx2, hy2]
    · -- Show that these points satisfy both equations
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · constructor
        · -- Check y^2 = x -1
          nlinarith
        · -- Check y = 2x - 2m^2 + m - 2
          ring_nf
      · constructor
        · -- Check y^2 = x -1
          nlinarith
        · -- Check y = 2x - 2m^2 + m - 2
          ring_nf
  rw [h1]
  by_cases h : m = 1/4
  · -- When m = 1/4, the two points are the same
    rw [h]
    norm_num
    <;> try { ring_nf }
    <;> try { simp }
    <;> try { norm_num }
    <;> try { tauto }
  · -- When m ≠ 1/4, the two points are different
    have h2 : (m^2 + 1) ≠ ( (4 * m^2 - 4 * m + 5)/4 ) := by
      by_contra h_eq
      have h_eq2 : 4 * (m^2 + 1) = 4 * m^2 - 4 * m + 5 := by
        linarith
      have h_eq3 : 4 * m = 1 := by
        nlinarith
      have h_eq4 : m = 1/4 := by
        linarith
      contradiction
    simp [Set.encard_pair, h2]
    <;> try { ring_nf }
    <;> try { simp }
    <;> try { norm_num }
    <;> try { tauto }
  all_goals
    try { ring_nf }
    <;> try { simp }
    <;> try { linarith }