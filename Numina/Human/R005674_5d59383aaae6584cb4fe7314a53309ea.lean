import Mathlib
set_option maxHeartbeats 500000

/- Find all ordered 4 -tuples of integers $(a, b, c, d)$ (not necessarily distinct) satisfying the following system of equations:
\[

$$
\begin{aligned}
a^{2}-b^{2}-c^{2}-d^{2} & =c-b-2 \\
2 a b & =a-d-32 \\
2 a c & =28-a-d \\
2 a d & =b+c+31
\end{aligned}
$$
\] -/

theorem algebra_609363 : {(a, b, c, d) : ℤ × ℤ × ℤ × ℤ | a ^ 2 - b ^ 2 - c ^ 2 - d ^ 2 = c - b - 2 ∧
  2 * a * b = a - d - 32 ∧ 2 * a * c = 28 - a - d ∧ 2 * a * d = b + c + 31} = {(5, -3, 2, 3)} := by
  ext ⟨a, b, c, d⟩
  constructor
  . -- Forward direction
    rintro ⟨h1, h2, h3, h4⟩
    have ha : a ≠ 0 := by
      by_contra ha0
      simp_all only [ha0]
      linarith
    have h2a : 2 * a ≠ 0 := by norm_num [ha]

    -- Derive the expression of $b$ and $c$ in the $ℚ$ domain
    have hb' : (b : ℚ) = (a - d - 32) / (2 * a) := by
      field_simp
      norm_cast
      rw [mul_comm, h2]
    have hc' : (c : ℚ) = (28 - a - d) / (2 * a) := by
      field_simp
      norm_cast
      rw [mul_comm, h3]

    -- Derive the expression of $b$ and $c$ in the $ℤ$ domain
    have hb : b = (a - d - 32) / (2 * a) := by
      rw [Int.eq_ediv_of_mul_eq_right h2a h2]
    have hc : c = (28 - a - d) / (2 * a) := by
      rw [Int.eq_ediv_of_mul_eq_right h2a h3]
    have h4' : 2 * a * (d : ℚ) = b + c + 31 := by
      norm_cast
    rw [hb', hc'] at h4'

    -- Derive the expression of $d$
    have hd : (2 * a ^ 2 + 1) * (d : ℚ) = 31 * a - 2 := by
      rw [← add_div] at h4'
      have hd1 : (a - d - 32 + (28 - a - d)) = (2 * (-d - 2) : ℚ) := by
        linarith
      simp [hd1] at h4'
      rw [div_add' _ _ _ (by norm_cast)] at h4'
      field_simp at h4' ⊢
      linarith

    -- Narrow down the scope of $a$
    have h_const : 2 * a ^ 2 + 1 ∣ 4 * a + 31 := by
      have h_const_1 : 2 * a ^ 2 + 1 ∣ 31 * a - 2 := by
        norm_cast at hd
        apply Dvd.intro at hd
        exact hd
      have h_const_2 : 4 * (a : ℚ) + 31 = 31 * (2 * (a : ℚ) ^ 2 + 1) - 2 * (a : ℚ) * (31 * (a : ℚ) - 2) := by nlinarith
      have h_const_3 : 2 * a ^ 2 + 1 ∣ 31 * (2 * a ^ 2 + 1) :=by norm_num
      have h_const_4 : 2 * a ^ 2 + 1 ∣ 2 * a * (31 * a - 2) := by
        have h_const_41 : 31 * a - 2 ∣ 2 * a * (31 * a - 2) :=by norm_num
        apply dvd_trans h_const_1 h_const_41
      norm_cast at h_const_2
      rw [h_const_2]
      apply dvd_sub h_const_3 h_const_4

    -- Calculate the value of $a$
    have h_range : |4 * (a : ℚ) + 31| ≥ |2 * (a : ℚ) ^ 2 + 1| := by
      rcases h_const with ⟨k, hk⟩
      norm_cast
      rw [hk]
      rw [abs_mul]
      apply le_mul_of_one_le_right
      simp [abs_nonneg]
      by_contra hfalse
      simp at hfalse
      simp [hfalse] at hk
      suffices Odd (4 * a + 31) by
        simp [hk] at this
      refine Int.odd_add'.mpr ⟨?_, fun _ => by omega⟩
      intro _
      refine Int.even_mul.mpr (by left; omega)
    have h_range_a : a ≥ -3 ∧ a ≤ 5 := by
      norm_cast at h_range
      rw [abs_of_nonneg (a := 2 * a^ 2 + 1)] at h_range
      by_contra hfalse
      rw [not_and_or] at hfalse
      rcases hfalse with (hleft | hright)
      -- Prove $a ≥ -3$
      . rw [Mathlib.Tactic.PushNeg.not_ge_eq] at hleft
        by_cases hnonneg : a ≤ -8
        -- Case when $a ≤ -8$
        . rw [abs_of_neg (by nlinarith)] at h_range
          have hchange : a ^ 2 + 2 * a + 16 ≤ 0 := by nlinarith
          have hchange_1 : a ^ 2 + 2 * a + 16 = (a + 1) ^ 2 + 15 := by ring_nf
          rw [hchange_1] at hchange
          have hover0 : 0 < (a + 1) ^ 2 + 15 := by nlinarith
          exact lt_irrefl 0 (lt_of_lt_of_le hover0 hchange)
        -- Case when $a > -8$
        . rw [Mathlib.Tactic.PushNeg.not_ge_eq] at hnonneg
          rw [abs_of_nonneg (by nlinarith)] at h_range
          have hchange : a ^ 2 - 2 * a - 15 ≤ 0 := by nlinarith
          have hchange1 : (a + 3) * (a - 5) = a ^ 2 - 2 * a - 15 := by ring_nf
          rw [←hchange1] at hchange
          have hf1 : 0 < (a + 3) * (a - 5) := by
            have hf11 : a + 3 < 0 := by nlinarith
            have hf12 : a - 5 < 0 := by nlinarith
            apply mul_pos_of_neg_of_neg hf11 hf12
          exact lt_irrefl 0 (lt_of_lt_of_le hf1 hchange)
      -- Prove $a ≤ 5$
      . rw [Mathlib.Tactic.PushNeg.not_ge_eq] at hright
        have hr1 : 4 * a + 31 ≥ 0 := by nlinarith
        rw [abs_of_nonneg hr1] at h_range
        have hchange : a ^ 2 - 2 * a - 15 ≤ 0 := by nlinarith
        have hchange1 : (a + 3) * (a - 5) = a ^ 2 - 2 * a - 15 := by ring_nf
        rw [←hchange1] at hchange
        have hf1 : 0 < (a + 3) * (a - 5) := by
          have hf11 : a + 3 > 0 := by nlinarith
          have hf12 : a - 5 > 0 := by nlinarith
          apply Right.mul_pos hf11 hf12
        exact lt_irrefl 0 (lt_of_lt_of_le hf1 hchange)
      nlinarith

    norm_cast at hd
    apply Int.eq_ediv_of_mul_eq_right (a := 2 * a ^ 2 + 1) (b := d) (c := 31 * a - 2) at hd
    . rcases h_range_a with ⟨hleft, hright⟩
      have haa : a = 5 ∨ a = -3 ∨ a = -2 ∨ a = -1 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by
        interval_cases a
        all_goals simp
        exact ha rfl
      have ha5 : a = 5 := by
        by_contra har
        have h_range_az : a = -3 ∨ a = -2 ∨ a = -1 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by tauto
        rcases h_range_az with (haz | haz |haz | haz | haz | haz | haz)
        all_goals
        -- Calculate the value of $b$, $c$, $d$ and prove that one of them is not an integer at least
        { simp [haz] at hd hb hc
          rw [haz, hb, hc, hd] at h1
          norm_num at h1}
      -- Calculate the value of $b$, $c$, $d$
      rw [ha5] at hd
      rw [ha5,hd] at hb hc
      simp at hb hc hd
      simp [ha5,hb,hc,hd]
    . nlinarith
  . -- Backward direction
    simp_all