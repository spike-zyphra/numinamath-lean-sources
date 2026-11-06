import Mathlib

/- The equality $3^{3}+4^{3}+5^{3}=6^{3}$ is known. Show that there are no other sets of four consecutive integers where the cube of the largest number equals the sum of the cubes of the other numbers, and furthermore, that there are no such sets of five consecutive integers with this property. -/
theorem number_theory_155760 (n : ℕ) (h : n > 0) :
    (n^3 + (n+1)^3 + (n+2)^3 = (n+3)^3 ↔ n = 3) ∧
    ¬∃ m, m > 0 ∧ m^3 + (m+1)^3 + (m+2)^3 + (m+3)^3 = (m+4)^3 := by

    constructor
    · -- part I
      constructor
      · intro h_cube_sum_eq
        by_contra! h_nne3 
        -- suppose it has another solution n, then either n < 3 or n > 3
        have : n < 3 ∨ n > 3 := by exact Nat.lt_or_gt_of_ne h_nne3
        rcases this with h | hn_gt
        · -- the case n < 3 can be ruled out easily
          interval_cases n  
          all_goals linarith
        -- if n > 3, we let n = x + 3
        let x : ℤ := (n : ℤ) - 3
        have hx_pos: x > 0 := by
          unfold x
          refine Int.sub_pos_of_lt ?h
          norm_cast
        have hn_eq_x_add_3 : n = x + 3 := by
          unfold x; symm;
          exact Int.sub_add_cancel (↑n) 3
        have h_n_eq_int : n ^ 3 + (n + 1) ^ 3 + (n + 2) ^ 3 = ((n + 3) ^ 3 : ℤ) := by norm_cast
        rw [hn_eq_x_add_3] at h_n_eq_int
        rw [← sub_eq_zero] at h_n_eq_int
        have : (x + 3) ^ 3 + (x + 3 + 1) ^ 3 + (x + 3 + 2) ^ 3 - (x + 3 + 3) ^ 3 = 2 * (x ^ 3 + 9 * x ^ 2 + 21 * x) := by ring
        rw [this] at h_n_eq_int -- then the equation is x ^ 3 + 9 * x ^ 2 + 21 * x = 0
        simp at h_n_eq_int
        rw [show x ^ 3 + 9 * x ^ 2 + 21 * x = x * (x ^ 2 + 9 * x + 21) by ring] at h_n_eq_int
        have : x ≠ 0 := by exact Ne.symm (Int.ne_of_lt hx_pos)
        simp [this] at h_n_eq_int
        -- as x ≠ 0, we must have x ^ 2 + 9 * x + 21 = 0
        -- but this is impossible
        have : x ^ 2 + 9 * x + 21 > 0 := by
          trans x ^ 2 + 9 * x
          · simp
          apply add_pos
          exact Lean.Omega.Int.pos_pow_of_pos x 2 hx_pos
          apply mul_pos
          norm_num
          exact hx_pos
        linarith
      · rintro rfl
        simp

    · -- part 2
      rintro ⟨y', ⟨_, hy'_cube_sum_eq⟩⟩
      let y : ℤ := ↑y'
      have hy_cube_sum_eq : y ^ 3 + (y + 1) ^ 3 + (y + 2) ^ 3 + (y + 3) ^ 3 = (y + 4) ^ 3 := by
        unfold y
        norm_cast
      rw [← sub_eq_zero] at hy_cube_sum_eq
      have : y ^ 3 + (y + 1) ^ 3 + (y + 2) ^ 3 + (y + 3) ^ 3 - (y + 4) ^ 3 =
        3 * (y ^ 3 + 2 * y ^ 2 - 2 * y) - 28 := by ring
      rw [this, sub_eq_zero] at hy_cube_sum_eq
      have : (3 : ℤ) ∣ 28 := by exact Dvd.intro (y ^ 3 + 2 * y ^ 2 - 2 * y) hy_cube_sum_eq
      norm_num at this
