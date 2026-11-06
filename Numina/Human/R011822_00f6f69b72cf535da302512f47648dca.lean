import Mathlib
open Real Complex  
noncomputable section

-- lemma : Prove that the floor of $sqrt(x)$ equals $z$ when $z^2 ≤ x < (z + 1)^2$.
lemma sqrt_floor_eq {x : ℝ} {z : ℤ} (hx : x ≥ 0) (hz : z ≥ 0)
    (h_bounds : z^2 ≤ x ∧ x < (z + 1)^2) :
    (Int.floor (sqrt x) : ℝ) = z := by
  -- Derive sqrt bounds: $sqrt(z^2) ≤ sqrt x < sqrt((z + 1)^2)$.
  have h_sqrt_bounds : sqrt (z^2) ≤ sqrt x ∧ sqrt x < sqrt ((z + 1)^2) := by
    split_ands
    · exact Real.sqrt_le_sqrt (by nlinarith : z^2 ≤ x)
    · exact Real.sqrt_lt_sqrt hx (by nlinarith : x < (z + 1)^2)
  have h_z_sqrt : sqrt (z^2) = z := by
    rw [sqrt_sq]
    exact_mod_cast hz
  have h_z_plus_one_sqrt : sqrt ((z + 1)^2) = z + 1 := by
    rw [sqrt_sq]
    exact_mod_cast add_nonneg hz zero_le_one
  have h_z_plus_one_cast : (z + 1 : ℝ) = z + 1 := by norm_num
  rw [h_z_sqrt, h_z_plus_one_sqrt, h_z_plus_one_cast] at h_sqrt_bounds
  -- Apply floor theorem to conclude $⌊sqrt x⌋ = z$.
  exact_mod_cast Int.floor_eq_iff.mpr h_sqrt_bounds

/-4・30 Find all solutions to the equation $x^{2}-8[x]+7=0$. Here, $[x]$ denotes the greatest integer less than or equal to $x$.-/
theorem algebra_212345 :
  ∀ x : ℝ, x^2 - 8 * (Int.floor x : ℝ) + 7 = 0 ↔ x = 1 ∨ x = Real.sqrt 33 ∨ x = Real.sqrt 41 ∨ x = 7 := by
  intro x
  constructor
  · intro h
    -- Conclude solution set: $x = 1$, $sqrt 33$, $sqrt 41$, or $7$.
    have h_solutions : x = 1 ∨ x = Real.sqrt 33 ∨ x = Real.sqrt 41 ∨ x = 7 := by
      have h' : x^2 - 8 * (Int.floor x : ℝ) + 7 = 0 := h
      have h_floor_le_x : (Int.floor x : ℝ) ≤ x := Int.floor_le x
      have h_x_lt_floor_plus_one : x < (Int.floor x : ℝ) + 1 := Int.lt_floor_add_one x
      have h_floor_pos : 0 < (Int.floor x : ℝ) := by
        by_contra h_floor_pos'
        have h_neg_floor : (Int.floor x : ℝ) ≤ 0 := by linarith
        nlinarith [h, sq_nonneg (x - 1), sq_nonneg (x - 7)]
      have h_floor_le_seven : (Int.floor x : ℤ) ≤ 7 := by
        by_contra h_floor_le_seven
        have h_floor_ge_eight : (Int.floor x : ℤ) ≥ 8 := by linarith
        have h_floor_large : (Int.floor x : ℝ) ≥ 8 := by exact_mod_cast h_floor_ge_eight
        nlinarith [h, sq_nonneg (x - 1), sq_nonneg (x - 7)]
      -- Enumerate valid floor values: $n = 1$, $5$, $6$, $7$.
      have h_valid_floors : (Int.floor x : ℤ) = 1 ∨ (Int.floor x : ℤ) = 5 ∨ (Int.floor x : ℤ) = 6 ∨ (Int.floor x : ℤ) = 7 := by
        have h_floor_gt_zero : (Int.floor x : ℤ) > 0 := by exact_mod_cast h_floor_pos
        have h_floor_le_seven : (Int.floor x : ℤ) ≤ 7 := h_floor_le_seven
        interval_cases (Int.floor x : ℤ) <;> norm_num at h' ⊢ <;>
          nlinarith [h, h_floor_le_x, h_x_lt_floor_plus_one, h_floor_pos,
            sq_nonneg (x - 1), sq_nonneg (x - 7),
            Real.sqrt_nonneg 33, Real.sqrt_nonneg 41,
            Real.sq_sqrt (show 0 ≤ 33 by norm_num), Real.sq_sqrt (show 0 ≤ 41 by norm_num)]
      rcases h_valid_floors with (h_floor_eq_n | h_floor_eq_n | h_floor_eq_n | h_floor_eq_n)
      · -- Case: floor $x = 1$.
        have h_floor_eq_one : (Int.floor x : ℝ) = 1 := by exact_mod_cast h_floor_eq_n
        have h_x_eq : x = 1 := by nlinarith [h, h_floor_eq_one, h_floor_le_x, h_x_lt_floor_plus_one]
        exact Or.inl h_x_eq
      · -- Case: floor $x = 5$.
        have h_floor_eq_five : (Int.floor x : ℝ) = 5 := by exact_mod_cast h_floor_eq_n
        have h_x_eq_sqrt : x = Real.sqrt 33 := by
          have h_x_ge_floor : x ≥ 5 := by linarith [h_floor_eq_five, h_floor_le_x]
          have h_x_lt_floor_plus_one : x < 6 := by linarith [h_floor_eq_five, h_x_lt_floor_plus_one]
          nlinarith [h, h_floor_eq_five, h_x_ge_floor, h_x_lt_floor_plus_one,
            Real.sqrt_nonneg 33, Real.sq_sqrt (show 0 ≤ 33 by norm_num)]
        exact Or.inr (Or.inl h_x_eq_sqrt)
      · -- Case: floor $x = 6$.
        have h_floor_eq_six : (Int.floor x : ℝ) = 6 := by exact_mod_cast h_floor_eq_n
        have h_x_eq_sqrt : x = Real.sqrt 41 := by
          have h_x_ge_floor : x ≥ 6 := by linarith [h_floor_eq_six, h_floor_le_x]
          have h_x_lt_floor_plus_one : x < 7 := by linarith [h_floor_eq_six, h_x_lt_floor_plus_one]
          nlinarith [h, h_floor_eq_six, h_x_ge_floor, h_x_lt_floor_plus_one,
            Real.sqrt_nonneg 41, Real.sq_sqrt (show 0 ≤ 41 by norm_num)]
        exact Or.inr (Or.inr (Or.inl h_x_eq_sqrt))
      · -- Case: floor $x = 7$.
        have h_floor_eq_seven : (Int.floor x : ℝ) = 7 := by exact_mod_cast h_floor_eq_n
        have h_x_eq : x = 7 := by nlinarith [h, h_floor_eq_seven, h_floor_le_x, h_x_lt_floor_plus_one]
        exact Or.inr (Or.inr (Or.inr h_x_eq))
    exact h_solutions
  · intro h
    -- Verify floor and equation for $x = 1$ ,$sqrt 33$, $sqrt 41$, $7$.
    rcases h with (rfl | rfl | rfl | rfl)
    · have h_floor_eq_one : (Int.floor (1 : ℝ) : ℝ) = 1 := by norm_num [Int.floor_eq_iff]
      norm_num [h_floor_eq_one]
    · have h_floor_eq_five : (Int.floor (Real.sqrt 33 : ℝ) : ℝ) = 5 := by
        apply sqrt_floor_eq <;> norm_num
      rw [h_floor_eq_five]
      norm_num [Real.sq_sqrt (show 0 ≤ 33 by norm_num)]
    · have h_floor_eq_six : (Int.floor (Real.sqrt 41 : ℝ) : ℝ) = 6 := by
        apply sqrt_floor_eq <;> norm_num
      rw [h_floor_eq_six]
      norm_num [Real.sq_sqrt (show 0 ≤ 41 by norm_num)]
    · have h_floor_eq_seven : (Int.floor (7 : ℝ) : ℝ) = 7 := by norm_num [Int.floor_eq_iff]
      norm_num [h_floor_eq_seven]
