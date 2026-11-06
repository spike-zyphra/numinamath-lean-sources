import Mathlib

open Real

set_option maxHeartbeats 0


/-
  Prove that for all nonnegative real numbers $a, b, c$ satisfying the condition $bc + ca + ab = a + b + c$, the inequality $a + b + c + 1 \ge 4abc$ holds.
-/
lemma add_one_ge_four_mul {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : b * c + c * a + a * b = a + b + c) :
    a + b + c + 1 ≥ 4 * (a * b * c) := by
  have habc : (b + c - 1) * a = b + c - b * c := by linarith only [habc]
  by_cases hne : b = 0 ∨ c = 0
  · -- if either b or c is zero, the inequality holds trivially
    rcases hne with h | h
    all_goals
      simp [h]
      positivity
  · -- otherwise, we have b > 0 and c > 0
    -- then a = (b + c - b * c) / (b + c - 1)
    simp at hne
    have hb : b > 0 := by
      apply lt_of_le_of_ne ?_
      apply Ne.symm hne.1
      assumption
    have hc : c > 0 := by
      apply lt_of_le_of_ne ?_
      apply Ne.symm hne.2
      assumption
    -- which also implies that b + c > 1
    have h₁ : b + c > 1 := by
      by_contra h
      simp at h
      rcases lt_or_eq_of_le h with h | h
      · have : (b + c - 1) * a ≤ 0 := by
          apply mul_nonpos_of_nonpos_of_nonneg
          · apply sub_nonpos.mpr
            apply le_of_lt h
          · exact ha
        rw [habc] at this
        have : ¬ b + c - b * c ≤ 0 := by
          push_neg
          trans c
          · exact hc
          · apply sub_pos.mp
            apply lt_of_lt_of_eq (b := b * (1 - c))
            · apply mul_pos hb
              simp
              trans b + c
              · exact lt_add_of_pos_left c hb
              · exact h
            · ring
        contradiction
      · simp [h] at habc
        have hbc : b * c = 1 := by linarith only [habc]
        have : (b - c) ^ 2 < 0 := by
          apply lt_of_eq_of_lt (b := -3) ?_ (by simp)
          trans (b + c) ^ 2 - 4 * (b * c)
          · ring
          · simp [h, hbc]
            norm_num
        have : ¬ (b - c) ^ 2 < 0 := by push_neg; positivity
        contradiction
    have h₂ : b + c - 1 > 0 := by apply sub_pos.mpr h₁
    have ha : a = (b + c - b * c) / (b + c - 1) := by
      field_simp
      rw [←habc]
      ring
    -- substituting a= (b + c - b * c) / (b + c - 1) into the inequality
    -- we have to show that b ^ 2 * (2 * c - 1) ^ 2 + b * (c + 1 - 4 * c ^ 2) + c ^ 2 + c - 1 ≥ 0
    rw [ha]
    apply sub_nonneg.mp
    field_simp
    apply div_nonneg ?_ (le_of_lt h₂)
    trans b ^ 2 * (2 * c - 1) ^ 2 + b * (c + 1 - 4 * c ^ 2) + c ^ 2 + c - 1
    · by_cases hc' : c =  1 / 2
      · simp [hc']
        norm_num
        trans (1 / 2) * (1 / 2) + 1 / 4 + (1 / 2: ℝ)
        · norm_num
        · gcongr
          simp [hc'] at h₁
          linarith only [h₁]
      · have h₃ : 2 * c - 1 ≠ 0 := by
          by_contra h
          have : c = 1 / 2 := by linarith only [h]
          simp [this] at hc'
        trans (2 * c - 1) ^ 2 * (b ^ 2 + b * (1 + c - 4 * c ^ 2) / (2 * c - 1) ^ 2 + (c ^ 2 + c - 1) / (2 * c - 1) ^ 2)
        · apply mul_nonneg
          · positivity
          · -- if c ≤ 5 /8, since b > 1 - c, it suffices to show that
            -- when b = 1 - c, the expression is nonnegative
            by_cases hc' : c ≤ 5 / 8
            · trans (1 - c) ^ 2 + (1 - c) * (1 + c - 4 * c ^ 2) / (2 * c - 1) ^ 2 + (c ^ 2 + c - 1) / (2 * c - 1) ^ 2
              · apply sub_nonneg.mp
                field_simp
                apply div_nonneg
                ring_nf
                trans (c ^ 2 - c + 1) * (2 * c - 1) ^ 2
                · apply mul_nonneg ?_ (by positivity)
                  trans (c - 1) ^ 2
                  · positivity
                  · apply sub_nonneg.mp
                    ring_nf
                    apply le_of_lt hc
                · apply le_of_eq
                  ring
                positivity
              · apply sub_nonneg.mp
                field_simp
                trans ((b + c - 1) * ((2 * c - 1) ^ 2 * (b - c + 1) + (1 + c - 4 * c ^ 2))) / (2 * c - 1) ^ 2
                · apply div_nonneg ?_ (by positivity)
                  apply mul_nonneg (by positivity)
                  trans (2 * c - 1) ^ 2 * ((1 - c) - c + 1) + (1 + c - 4 * c ^ 2)
                  · apply sub_nonneg.mp
                    ring_nf
                    trans 3 - (5 / 8) * 9 + ((5 / 8) ^ 2 * 12 - (5 / 8 : ℚ) ^ 3 * 8)
                    · norm_num
                    · apply sub_nonneg.mp
                      trans - (c - 5 / 8) * (8 * (c ^ 2 + 5 / 8 * c + (5 / 8) ^ 2) - 12 * (c + 5 / 8) + 9)
                      · apply mul_nonneg
                        · simp
                          exact hc'
                        · ring_nf
                          trans 8 * (c - 7 / 16) ^ 2 + (37 / 8 - (7 / 16) ^ 2 * 8)
                          · apply add_nonneg
                            · positivity
                            · norm_num
                          · apply le_of_eq
                            ring
                      · apply le_of_eq
                        ring
                  · apply sub_nonneg.mp
                    trans (2 * c - 1) ^ 2 * (b + c - 1)
                    · apply mul_nonneg (by positivity)
                      apply le_of_lt h₂
                    · apply le_of_eq
                      ring
                · apply le_of_eq
                  congr 1
                  ring
            · -- otherwise, we have c > 5 / 8
              -- then the minimum of the expression occurs at b = - (c + 1 - 4 * c ^ 2) / (2 * c - 1) ^ 2 / 2
              push_neg at hc'
              trans (b + (c + 1 - 4 * c ^ 2) / (2 * c - 1) ^ 2 / 2) ^ 2 + ((c ^ 2 + c - 1) / (2 * c - 1) ^ 2 - ((c + 1 - 4 * c ^ 2) / (2 * c - 1) ^ 2) ^ 2 / 4)
              · apply add_nonneg
                · positivity
                · field_simp
                  apply div_nonneg
                  · trans (2 * c - 1) ^ 2 * (c - 1) ^ 2 * (8  * c - 5)
                    · apply mul_nonneg
                      · positivity
                      · simp
                        linarith only [hc']
                    · apply le_of_eq
                      ring
                  · positivity
              · apply le_of_eq
                ring
        · apply le_of_eq
          field_simp
          ring
    · apply le_of_eq
      ring

/-
Determine the maximum value of $n$ such that the inequality $a + b + c + 1 \ge 4(abc)^n$ holds for all nonnegative real numbers $a, b, c$ satisfying the condition $bc + ca + ab = a + b + c$.
-/
theorem  inequalities_617984 :
    IsGreatest {n : ℝ | ∀ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ b * c + c * a + a * b = a + b + c → a + b + c + 1 ≥ 4 * (a * b * c) ^ n} 1 := by
  constructor
  · simp
    apply add_one_ge_four_mul
  · -- we show that for any n > 1, there exist a, b, c such that the inequality does not hold
    simp [upperBounds]
    intro n hn
    by_contra h
    simp at h
    -- let ε = 1 / 8 ^ (1 / (n - 1) + 2) / 2
    -- b = 1 / 2 + ε, c = 1 / 2 + ε, and a be the root of the equation a + b + c = a * b + b * c + c * a
    let ε : ℝ := 1 / 8 ^ (1 / (n - 1) + 2) / 2
    have hε : ε > 0 := by
      simp [ε]
      apply rpow_pos_of_pos
      simp
    have hε_lt : ε < 1 / 8 ^ (1 / (n - 1) + 2) := by
      simp [ε]
      apply rpow_pos_of_pos
      simp
    have hε' : ε < 1 / 2 := by
      apply lt_trans hε_lt
      trans 1 / 64
      · gcongr
        rw [rpow_add]
        norm_num
        · apply one_lt_rpow
          · simp
          · simp [h]
        · simp
      · norm_num
    let b := 1 / 2 + ε
    let c := 1 / 2 + ε
    let a := (3 + 4 * ε - 4 * ε ^ 2) / (8 * ε)
    have ha : 0 < a := by
      apply div_pos
      · apply lt_of_lt_of_eq (b := 4 - (2 * ε - 1) ^ 2)
        · simp
          nlinarith only [hε, hε']
        · ring
      · positivity
    have haε : 32 * a * ε ≥ 3 := by
      field_simp [a]
      apply le_div_iff₀ ?_|>.mpr
      apply sub_nonneg.mp
      ring_nf
      apply add_nonneg
      · positivity
      · trans 128 * ε ^ 2 * (1 - ε)
        · apply mul_nonneg
          · positivity
          · simp
            apply le_trans (le_of_lt hε')
            norm_num
        · apply le_of_eq
          ring
      positivity
    have ha' : a > 4 * 8 ^ (1 / (n - 1)) := by
      trans 2 / (32 * ε)
      · apply sub_pos.mp
        field_simp
        apply lt_of_lt_of_le (b := 3)
        · norm_num
        · apply le_trans haε
          apply le_of_eq
          ring
      · apply lt_of_eq_of_lt (b := 2 / (32 * (1 / 8 ^ (1 / (n - 1) + 2))))
        · field_simp
          rw [rpow_add]
          ring
          simp
        · gcongr
    have hb : 0 ≤ b := by positivity
    have hc : 0 ≤ c := by positivity
    have habc : b * c + c * a + a * b = a + b + c := by
      simp [a, b, c]
      field_simp
      ring
    apply hn a b c (le_of_lt ha) hb hc at habc
    simp [b, c] at habc
    -- We only need to show that a + b + c + 1 < 4 * (a * b * c) ^ n
    have h₁ : 4 * (a / 4) ^ n * (1 + 2 * ε) ^ (2 * n) ≤ a + 2 * ε + 2 := by
      apply le_of_eq_of_le ?_ (le_of_le_of_eq habc ?_)
      · field_simp
        norm_num
        trans 4 * (a / 4) ^ n * ((1 + 2 * ε) * (1 + 2 * ε)) ^ n
        · congr 1
          rw [rpow_mul]
          congr
          norm_cast
          rw [sq]
          positivity
        · rw [mul_assoc, ←mul_rpow]
          congr 2
          ring
          all_goals positivity
      · ring
    -- Equivalently, we need to show that 4 * (a / 4) ^ n * (1 + 2 * ε) ^ (2 * n) > 8 * a * (1 + 4 * n * ε)
    have h₂ : (1 + 2 * ε) ^ (2 * n) ≥ 1 + 2 * n * (2 * ε) := by
      apply one_add_mul_self_le_rpow_one_add
      · trans 0
        · simp
        · positivity
      · trans 2
        · simp
        · simp
          apply le_of_lt h
    -- It suffices to show that (a / 4) ^ n > 2 * a and (1 + 2 * ε) ^ (2 * n) > 1 + 2 * n * (2 * ε) by the Bernoulli's inequality
    have h₃ : (a / 4) ^ n > 2 * a := by
      have : (a / 4) ^ (n - 1) > 8 := by
        apply lt_of_eq_of_lt (b := (4 * 8 ^ (1 / (n - 1)) / 4) ^ (n - 1))
        · field_simp
          rw [←rpow_mul]
          have : n - 1 > 0 := by simp; exact h
          field_simp
          simp
        · gcongr
          simp [h]
      rw [rpow_sub] at this
      apply lt_div_iff₀ (by simp; positivity) |>.mp at this
      apply lt_of_eq_of_lt ?_ this
      field_simp
      ring
      positivity
    have h₃ : 4 * (a / 4) ^ n * (1 + 2 * ε) ^ (2 * n) > 8 * a * (1 + 4 * n * ε) := by
      apply mul_lt_mul_of_lt_of_le_of_pos_of_nonneg
      · apply lt_of_eq_of_lt (b := 4 * (2 * a))
        · ring
        · apply mul_lt_mul_of_pos_left h₃
          simp
      · apply le_trans ?_ h₂
        apply le_of_eq
        ring
      · positivity
      · positivity
    have h₄ : ¬ 4 * (a / 4) ^ n * (1 + 2 * ε) ^ (2 * n) ≤ a + 2 * ε + 2 := by
      push_neg
      apply lt_of_le_of_lt ?_ h₃
      rw [mul_add, add_assoc]
      apply add_le_add
      · apply sub_nonneg.mp
        rw [mul_one]
        apply le_of_le_of_eq (b := 7 * a)
        · positivity
        · ring
      · trans 8 * a * (4 * 1 * ε)
        · simp
          apply le_of_le_of_eq (b := 32 * a * ε)
          · apply le_trans ?_ haε
            linarith only [hε']
          · ring
        · apply mul_le_mul_of_nonneg_left
          · apply mul_le_mul_of_nonneg_right
            · apply mul_le_mul_of_nonneg_left
              · apply le_of_lt h
              · simp
            · positivity
          · positivity
    contradiction
