import Mathlib

-- /- Example 5 Set $A=\{(x, y) \mid y=a x+1\}, B=\{(x, y) \mid y=| x |\}$, and $A \cap B$ is a singleton set, find the range of real number $a$. -/
theorem algebra_149681 (a : ℝ) (A B : Set (ℝ × ℝ))
  (hA : A = {(x, y) | y = a * x + 1})
  (hB : B = {(x, y) | y = abs x}) :
  (∃! p : ℝ × ℝ, p ∈ A ∧ p ∈ B) ↔ a ≥ 1 ∨ a ≤ -1 := by

  -- case by case analysis
  constructor
  . intro h
    by_cases ha : a ≥ 0
    · -- Case: a ≥ 0
      -- For x ≥ 0: ax + 1 = x, so x(a-1) = -1
      -- For x < 0: ax + 1 = -x, so x(a+1) = -1
      by_cases ha1 : a = 1
      · -- If a = 1, line is y = x + 1, intersects y = |x| at one point
        left
        rw [ha1]
      · -- If a ≠ 1 and a ≥ 0
        have : a > 1 ∨ (a < 1 ∧ a ≥ 0) := by
          cases' lt_or_gt_of_ne ha1 with h1 h2
          · right; exact ⟨h1, ha⟩
          · left; exact h2
        cases' this with h1 h2
        · left; linarith
        · -- This case leads to two intersection points, contradicting singleton
          exfalso
          rcases h with ⟨p, hp⟩
          set p1 := (1 / (1 - a), 1 / (1 - a))
          have h₁ : 0 < 1 - a := by linarith
          have hp1 : p1 ∈ A ∧ p1 ∈ B := by
            rw [hA, hB]
            constructor
            · field_simp [h₁]
            · have h₂ : 0 < 1 / (1 - a) := div_pos (by norm_num) h₁
              field_simp [abs_of_pos h₂]
          set p2 := (-1 / (a + 1), 1 / (a + 1))
          have hp2 : p2 ∈ A ∧ p2 ∈ B := by
            rw [hA, hB]
            constructor
            . field_simp
            . have h₂ : -1 / (a + 1) < 0 := by
                have : a + 1 > 0 := by linarith
                exact div_neg_of_neg_of_pos (by norm_num) this
              field_simp [abs_of_neg h₂]
          have nep12 : p1 ≠ p2 := by
            unfold p1 p2
            by_contra eqh
            rw [Prod.mk.inj_iff] at eqh
            rcases eqh with ⟨eqh1, eqh2⟩
            have h₁ : 0 < 1 / (1 - a) := one_div_pos.mpr h₁
            have h₂ : -1 / (a + 1) < 0 := by
              have : a + 1 > 0 := by linarith
              exact div_neg_of_neg_of_pos (by norm_num) this
            linarith
          have h1 : p1 = p := hp.2 p1 hp1
          have h2 : p2 = p := hp.2 p2 hp2
          have : p1 = p2 := by rw [←h2] at h1; exact h1
          tauto
    · -- Case: a < 0
      push_neg at ha
      by_cases ha1 : a = -1
      · right
        rw [ha1]
      · -- If a ≠ -1 and a < 0
        push_neg at ha1
        symm at ha1
        have : a > -1 ∨ a < -1 := lt_or_gt_of_ne ha1
        cases' this with h1 h2
        · -- This case leads to two intersection points, contradicting singleton
          exfalso
          have h₁ : 0 < 1 - a := by linarith
          rcases h with ⟨p, hp⟩
          set p1 := (1 / (1 - a), 1 / (1 - a))
          have hp1 : p1 ∈ A ∧ p1 ∈ B := by
            rw [hA, hB]
            constructor
            . field_simp
            . have : 0 < 1 / (1 - a) := by simp [h₁]
              field_simp [abs_of_pos this]
          set p2 := (-1 / (a + 1), 1 / (a + 1))
          have hp2 : p2 ∈ A ∧ p2 ∈ B := by
            rw [hA, hB]
            have h0: a + 1 > 0 := by linarith
            constructor
            . field_simp
            . have : -1 / (a + 1) < 0 := by
                exact div_neg_of_neg_of_pos (by norm_num) h0
              field_simp [abs_of_neg this]
          have nep12 : p1 ≠ p2 := by
            unfold p1 p2
            by_contra eqh
            rw [Prod.mk.inj_iff] at eqh
            rcases eqh with ⟨eqh1, eqh2⟩
            have h₁ : 0 < 1 / (1 - a) := one_div_pos.mpr h₁
            have h₂ : -1 / (a + 1) < 0 := by
              have : a + 1 > 0 := by linarith
              exact div_neg_of_neg_of_pos (by norm_num) this
            linarith
          have h1 : p1 = p := hp.2 p1 hp1
          have h2 : p2 = p := hp.2 p2 hp2
          have : p1 = p2 := by rw [←h2] at h1; exact h1
          tauto
        · right; exact le_of_lt h2
  . intro h
    rcases h with hp | hn
    . use (-1 / (a + 1), 1 / (a + 1))
      have pa: a + 1 > 0 := by linarith
      have na: -1 / (a + 1) < 0 := div_neg_of_neg_of_pos (by norm_num) pa
      constructor
      . field_simp [hA, hB, abs_of_neg na]
      . intro ⟨x, y⟩ ⟨iA, iB⟩
        simp [hA] at iA
        simp [hB] at iB
        rw [Prod.mk.inj_iff]
        by_cases px : x ≥ 0
        . rw [abs_of_nonneg px] at iB
          by_cases a1 : a = 1
          . simp [iB, a1] at iA
          . have solx : x = 1 / (1 - a) := by
              rw [iB] at iA
              rw [div_eq_of_eq_mul]
              exact sub_ne_zero_of_ne (id (Ne.symm a1))
              linarith
            have negx : x < 0 := by
              rw [solx]
              apply div_neg_of_pos_of_neg (by norm_num)
              apply lt_of_le_of_ne (by linarith)
              push_neg at a1
              exact sub_ne_zero_of_ne (id (Ne.symm a1))
            exfalso
            exact not_lt_of_ge px negx
        . push_neg at px
          rw [abs_of_neg px] at iB
          rw [iB] at iA
          constructor
          rw [div_eq_of_eq_mul]
          exact ne_of_gt pa
          linarith
          rw [iB]
          rw [div_eq_of_eq_mul]
          exact ne_of_gt pa
          linarith
    . use (1 / (1 - a), 1 / (1 - a))
      have pa : 1 - a > 0 := by linarith
      have na : 1 / (1 - a) > 0 := div_pos (by norm_num) pa
      constructor
      . field_simp [hA, hB, abs_of_pos na]
      . intro ⟨x, y⟩ ⟨iA, iB⟩
        simp [hA] at iA
        simp [hB] at iB
        rw [Prod.mk.inj_iff]
        by_cases px : x ≥ 0
        . rw [abs_of_nonneg px] at iB
          rw [iB] at iA
          constructor
          rw [div_eq_of_eq_mul]
          exact ne_of_gt pa
          linarith
          rw [iB, div_eq_of_eq_mul]
          exact ne_of_gt pa
          linarith
        . push_neg at px
          rw [abs_of_neg px] at iB
          by_cases am1 : a = -1
          . simp [iB, am1] at iA
          . have solx : x = -1 / (a + 1) := by
              rw [iB] at iA
              rw [div_eq_of_eq_mul]
              push_neg at am1
              let tmp := sub_ne_zero_of_ne am1
              simp at tmp
              tauto
              linarith
            have posx : x > 0 := by
              rw [solx]
              apply div_pos_of_neg_of_neg (by norm_num)
              apply lt_of_le_of_ne
              linarith
              push_neg at am1
              let tmp := sub_ne_zero_of_ne am1
              simp at tmp
              tauto
            exfalso
            exact not_lt_of_gt px posx
