import Mathlib

theorem algebra_20528 {a : ℕ+ → ℝ} (ha : ∃ r, ∀ n, a n = a 1 * r ^ (n.val - 1)) (hpos : ∀ n, a n > 0)
    (h : a 5 - a 4 = 576) (h' : a 2 - a 1 = 9) :
    a 1 + a 2 + a 3 + a 4 + a 5 = 1023 := by
  rcases ha with ⟨r, hr⟩
  have ha5 : a 5 = a 1 * r ^ 4 := by
    specialize hr 5
    simpa using hr
  have ha4 : a 4 = a 1 * r ^ 3 := by
    specialize hr 4
    simpa using hr
  have ha2 : a 2 = a 1 * r ^ 1 := by
    specialize hr 2
    simpa using hr
  rw [ha5, ha4] at h
  rw [ha2] at h'
  have eq1 : a 1 * r ^ 4 - a 1 * r ^ 3 = a 1 * r ^ 3 * (r - 1) := by ring
  have eq2 : a 1 * r ^ 1 - a 1 = a 1 * (r - 1) := by ring
  rw [eq1] at h
  rw [eq2] at h'
  have eq3 : r ^ 3 = 64 := by
    have h1 : a 1 * (r - 1) = 9 := by linarith
    have h2 : a 1 * r ^ 3 * (r - 1) = 576 := by linarith
    have h3 : a 1 * r ^ 3 * (r - 1) = (a 1 * (r - 1) ) * r ^ 3 := by ring
    rw [h3] at h2
    rw [h1] at h2
    nlinarith
  have hr4 : r = 4 := by
    have h1 : r ^ 3 = 64 := eq3
    have h2 : r ^ 3 - 64 = 0 := by linarith
    have h3 : r ^ 3 - 64 = (r - 4) * (r ^ 2 + 4 * r + 16) := by ring_nf
    rw [h3] at h2
    cases' (mul_eq_zero.mp h2) with h5 h6
    · linarith
    · -- The quadratic r^2 + 4 * r + 16 = 0 has no real solutions
      nlinarith [sq_nonneg (r + 2)]
  have ha1 : a 1 = 3 := by
    rw [hr4] at h'
    nlinarith [hpos 1]
  have ha2' : a 2 = 12 := by
    rw [ha2]
    rw [ha1, hr4]
    norm_num
  have ha3 : a 3 = 48 := by
    have ha3' : a 3 = a 1 * r ^ 2 := by
      specialize hr 3
      simpa using hr
    rw [ha3']
    rw [ha1]
    rw [hr4]
    norm_num
  have ha4' : a 4 = 192 := by
    rw [ha4]
    rw [ha1, hr4]
    norm_num
  have ha5' : a 5 = 768 := by
    rw [ha5]
    rw [ha1, hr4]
    norm_num
  linarith [ha1, ha2', ha3, ha4', ha5']