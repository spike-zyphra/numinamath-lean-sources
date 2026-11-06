import Mathlib

theorem algebra_199148 (x y z : ℤ) (h : ∃ n, x = n ∧ y = n + 1 ∧ z = n + 2) :
    x * (x + y + z) = x * y * z ↔ (x = -1 ∧ y = 0 ∧ z = 1) ∨ (x = 0 ∧ y = 1 ∧ z = 2) ∨ (x = 1 ∧ y = 2 ∧ z = 3) := by
  constructor
  · -- Assume x * (x + y + z) = x * y * z, need to prove the disjunction of the three triples.
    rintro h_eq
    rcases h with ⟨n, hx, hy, hz⟩
    rw [hx] at h_eq
    rw [hy] at h_eq
    rw [hz] at h_eq
    have h_eq6 : n * (n - 1) * (n + 1) = 0 := by
      ring_nf at h_eq ⊢
      nlinarith [sq_nonneg (n), sq_nonneg (n + 1), sq_nonneg ((n * (n + 1))), sq_nonneg ((n * n)), sq_nonneg ((n * (n + 1)))]
    cases' (mul_eq_zero.mp h_eq6) with h_eq7 h_eq8
    · -- Now h_eq7: n * (n - 1) = 0
      cases' (mul_eq_zero.mp h_eq7) with h_eq8 h_eq9
      · -- Now h_eq8: n = 0
        have hn0 : n = 0 := by 
          linarith
        have hx0 : x = 0 := by 
          nlinarith [hx, hn0]
        have hy1 : y = 1 := by 
          nlinarith [hy, hn0]
        have hz2 : z = 2 := by 
          nlinarith [hz, hn0]
        simp [hx0, hy1, hz2]
      · -- Now h_eq9: n - 1 = 0
        have hn1 : n = 1 := by 
          linarith
        have hx1 : x = 1 := by 
          nlinarith [hx, hn1]
        have hy2 : y = 2 := by 
          nlinarith [hy, hn1]
        have hz3 : z = 3 := by 
          nlinarith [hz, hn1]
        simp [hx1, hy2, hz3]
    · -- Now h_eq8: n + 1 = 0
      have hn2 : n = -1 := by 
        linarith
      have hx2 : x = -1 := by 
        nlinarith [hx, hn2]
      have hy0 : y = 0 := by 
        nlinarith [hy, hn2]
      have hz1 : z = 1 := by 
        nlinarith [hz, hn2]
      simp [hx2, hy0, hz1]
  · -- Assume the disjunction. Need to prove the equation x · (x + y + z) = x · y · z
    rintro (h | h | h)
    · -- First disjunction
      rcases h with ⟨hx, hy, hz⟩
      rw [hx, hy, hz]
      norm_num
    · -- Second disjunction
      rcases h with ⟨hx, hy, hz⟩
      rw [hx, hy, hz]
      norm_num
    · -- Third disjunction
      rcases h with ⟨hx, hy, hz⟩
      rw [hx, hy, hz]
      norm_num
  all_goals nlinarith