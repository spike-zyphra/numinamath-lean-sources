import Mathlib
theorem algebra_178148 :
    IsGreatest {t : ℤ | ∃ x y z, t = x^2 + y^2 + z^2 ∧ x * y + x + y = 20 ∧ y * z + z + y = 6 ∧ x * z + x + z = 2} 84 := by 
  constructor 
  · -- Show 84 is in the set
    use -4, -8, -2 
    all_goals norm_num 
  · -- Show there is no greater element in the set 
    intro t ht 
    rcases ht with ⟨x, y, z, ht_eq, h1, h2, h3⟩ 
    have h4 : (x + 1) * (y + 1) = 21 := by 
      nlinarith 
    have h5 : (y + 1) * (z + 1) = 7 := by
      nlinarith 
    have h6 : (x + 1) * (z + 1) = 3 := by
      nlinarith 
    have h7 : 7 * (x + 1) = 3 * (y + 1) := by 
      have h8 : (y + 1) * (z + 1) = 7 := by linarith [h5] 
      have h9 : (x + 1) * (z + 1) = 3 := by linarith [h6] 
      have h10 : (y + 1 : ℤ) ≠ 0 := by 
        by_contra h 
        have : (y + 1) * (z + 1) = 0 := by 
          rw [h] 
          all_goals nlinarith 
        linarith [h8, this] 
      have h11 : (z + 1 : ℤ) ≠ 0 := by 
        by_contra h 
        have : (x + 1) * (z + 1) = 0 := by
          rw [h]
          all_goals nlinarith 
        linarith [h9, this] 
      have h12 : (z + 1) * (7 * (x + 1) - 3 * (y + 1)) = 0 := by 
        nlinarith 
      cases' (mul_eq_zero.mp h12) with h13 h14 
      · -- z + 1 = 0 
        exfalso 
        nlinarith 
      · -- 7 * (x + 1) - 3 * (y + 1) = 0 
        nlinarith 
    have h8 : ∃ k : ℤ, x + 1 = 3 * k := by 
      have h9 : (7 * (x + 1) : ℤ) % 3 = 0 := by
        omega 
      have h10 : (x + 1 : ℤ) % 3 = 0 := by 
        omega 
      refine' ⟨(x + 1) / 3, by omega⟩ 
    rcases h8 with ⟨k, hk⟩ 
    have h9 : y + 1 = 7 * k := by 
      nlinarith [h7, hk]
    have h10 : k^2 = 1 := by
      have eq1 : (x + 1) * (y + 1) = 21 := h4 
      rw [show x + 1 = 3 * k by linarith [hk] ] at eq1 
      rw [show y + 1 = 7 * k by linarith [h9] ] at eq1 
      have eq2 : (3 * k) * (7 * k) = 21 := eq1 
      have eq3 : 21 * k^2 = 21 := by 
        nlinarith 
      have eq4 : k^2 = 1 := by 
        have eq5 : 21 * k^2 = 21 * 1 := by 
          linarith 
        have h11 : (21 : ℤ) * k^2 = (21 : ℤ) * 1 := eq5 
        -- We use the fact that if a non-zero number times x and times y are equal, then x = y.
        have h12 : k^2 = 1 := by
          apply (mul_left_inj' (show (21 : ℤ) ≠ 0 by norm_num)).mp 
          linarith 
        assumption 
      assumption 
    have h11 : k = 1 ∨ k = -1 := by 
      rw [sq_eq_one_iff] at h10
      tauto 
    rcases h11 with (h12 | h13) 
    · -- k = 1 
      have hx1 : x = 2 := by 
        nlinarith [hk, h12] 
      have hy1 : y = 6 := by 
        nlinarith [h9, h12] 
      have hz1 : z = 0 := by 
        nlinarith [h6, h12, hx1] 
      rw [ht_eq] 
      rw [hx1, hy1, hz1] 
      all_goals nlinarith 
    · -- k = -1 
      have hx1 : x = -4 := by 
        nlinarith [hk, h13] 
      have hy1 : y = -8 := by 
        nlinarith [h9, h13] 
      have hz1 : z = -2 := by 
        nlinarith [h6, h13, hx1] 
      rw [ht_eq] 
      rw [hx1, hy1, hz1] 
      all_goals nlinarith