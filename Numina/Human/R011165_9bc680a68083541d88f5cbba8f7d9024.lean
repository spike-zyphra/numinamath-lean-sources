import Mathlib

open Real

/--
Problem statement (Main theorem of this file):
11.2. Find all values of the parameter $a$ for which the equation $\sqrt{x^{2}-2 x-3}\left(x^{2}-3 a x+2 a^{2}\right)=0$ has exactly three roots.

Solution:
Ответ: $-1 \leq a < -\frac{1}{2}$ или $\frac{3}{2} < a \leq 3$. Решение. См. задачу 10.2.

-/


theorem algebra_231353 (a : ℝ) :
  {x | x ^ 2 - 2 * x - 3 ≥ 0 ∧ sqrt (x ^ 2 - 2 * x - 3) * (x ^ 2 - 3 * a * x + 2 * a ^ 2) = 0}.encard = 3 ↔
  (-1 ≤ a ∧ a < -1 / 2) ∨ (3 / 2 < a ∧ a ≤ 3) := by
  constructor
  . intro h_card
    have h1 : {x | x ^ 2 - 2 * x - 3 ≥ 0 ∧ √(x ^ 2 - 2 * x - 3) * (x ^ 2 - 3 * a * x + 2 * a ^ 2) = 0} = {x | x ^ 2 - 2 * x - 3 ≥ 0 ∧ (x = 3 ∨ x = -1 ∨ x = a ∨ x = 2 * a)} := by
      ext x
      simp only [Set.mem_setOf_eq]
      constructor
      . intro ⟨hx1, hx2⟩

        have h_right: (x = 3 ∨ x = -1 ∨ x = a ∨ x = 2 * a) := by
          simp at hx2
          cases' hx2 with hx3 hx4
          . rw [sqrt_eq_zero hx1] at hx3
            have : (x - 3) * (x + 1) = 0 := by linarith
            simp at this
            cases this
            . left; linarith
            . right; left; linarith
          . right; right;
            have : (x - a) * (x - 2 * a) = 0 := by linarith
            simp at this
            cases this
            . left; linarith
            . right; linarith

        exact ⟨ hx1, h_right⟩

      . intro ⟨hx1, hx2⟩
        have h_right: √(x ^ 2 - 2 * x - 3) * (x ^ 2 - 3 * a * x + 2 * a ^ 2) = 0 := by
          simp
          rcases hx2 with rfl | rfl | ha | ha
          . left; norm_num
          . left; norm_num
          . right; rw [ha]; ring_nf
          . right; rw [ha]; ring_nf
        exact ⟨hx1, h_right⟩

    rw [h1] at h_card

    by_cases ha1: a ≥ -1/2 ∧ a ≤ 3 / 2
    . have : {x | x ^ 2 - 2 * x - 3 ≥ 0 ∧ (x = 3 ∨ x = -1 ∨ x = a ∨ x = 2 * a)} = {3, -1} := by
        ext x
        simp only [Set.mem_setOf_eq]
        constructor
        . intro ⟨hx1, hx2⟩
          rcases hx2 with rfl | rfl | ha | ha
          . simp
          . simp
          . rw [ha] at hx1
            rw [(by ring: a ^ 2 - 2 * a - 3 = (a-3) * (a+1))] at hx1
            by_cases ha2: a > 3
            . linarith
            . by_cases ha3: a = 3
              . linarith
              . by_cases ha4: a > -1
                . nlinarith
                . linarith
          . rw [ha] at hx1
            rw [(by ring: (2 * a) ^ 2 - 2 * (2 * a) - 3 = (2*a-3) * (2*a+1))] at hx1
            by_cases ha2: a > 3 / 2
            . linarith
            . by_cases ha3: a = 3 / 2
              . rw [ha3] at ha
                left; linarith
              . by_cases ha4: a > -1 / 2
                . push_neg at ha2
                  have : a < 3/2 := lt_of_le_of_ne ha2 ha3
                  nlinarith
                . by_cases ha5: a = -1 / 2
                  . rw [ha5] at ha
                    right; simp; linarith
                  . push_neg at ha4
                    have : a < -1/2 := lt_of_le_of_ne ha4 ha5
                    nlinarith

        . intro hx
          cases' hx with hx1 hx2
          . rw [hx1]
            simp
            norm_num
          . rw [hx2]
            simp
            norm_num


      rw [this] at h_card
      rw [Set.encard_pair (by norm_num)] at h_card
      contradiction

    . by_cases ha2: a > 3 ∨ a < -1
      . have : {x | x ^ 2 - 2 * x - 3 ≥ 0 ∧ (x = 3 ∨ x = -1 ∨ x = a ∨ x = 2 * a)} = {3, -1, a, 2*a} := by
          ext x
          simp only [Set.mem_setOf_eq]
          constructor
          . intro ⟨hx1, hx2⟩
            exact hx2
          . intro hx
            have h_left: x ^ 2 - 2 * x - 3 ≥ 0 := by
              rcases hx with rfl | rfl | ha | ha
              . linarith
              . linarith
              . rw [ha]
                cases ha2
                . nlinarith
                . nlinarith
              . rw [ha]
                cases ha2
                . nlinarith
                . nlinarith
            exact ⟨h_left, hx⟩

        rw [this] at h_card
        rw [Set.encard_insert_of_not_mem] at h_card
        rw [Set.encard_insert_of_not_mem] at h_card

        have : a ≠ 2 * a := by
          by_contra h
          cases ha2
          . linarith
          . linarith

        rw [Set.encard_pair this] at h_card
        norm_num at h_card
        . -- ⊢ -1 ∉ {a, 2 * a}
          by_contra h
          simp at h
          cases h
          . have : a = -1 := by linarith
            cases ha2
            . linarith
            . linarith
          . have : a = -1/2 := by linarith
            cases ha2
            . linarith
            . linarith

        . -- 3 ∉ {-1, a, 2 * a}
          by_contra h
          simp at h
          rcases h with h | h | h
          . linarith
          . rw [← h] at ha2
            cases ha2
            . linarith
            . linarith
          . have : a = 3/2 := by linarith
            rw [this] at ha2
            cases ha2
            . linarith
            . linarith

      . simp at ha1
        simp at ha2
        by_cases ha3: a < -1/2
        . left; exact ⟨ha2.2, ha3⟩
        . right
          push_neg at ha3
          exact ⟨ha1 ha3, ha2.1⟩

  . intro ha
    rw [Set.encard_eq_three]
    use -1, 3, (2*a)
    constructor
    . linarith
    . constructor
      . by_contra h
        have : a = -1/2 := by linarith
        rw [this] at ha
        simp at ha
        linarith
      . constructor
        . by_contra h
          have : a = 3/2 := by linarith
          rw [this] at ha
          simp at ha
          linarith
        . ext x
          simp only [Set.mem_setOf_eq]
          constructor
          . intro ⟨hx1,hx2⟩
            simp at hx2
            rw [sqrt_eq_zero] at hx2
            cases hx2
            . have : (x-3) * (x+1) = 0 := by linarith
              simp at this
              cases this
              . right;left; linarith
              . left; linarith
            . have : (x-a) * (x-2*a) = 0 := by linarith
              simp at this
              cases this
              . have : x = a := by linarith
                rw [this] at hx1
                rw [(by ring: a ^ 2 - 2 * a - 3 = (a-3) * (a+1))] at hx1
                by_cases ha1 : a > 3
                . cases ha
                  . linarith
                  . linarith
                . by_cases ha2 : a = 3
                  . right; left; linarith
                  . by_cases ha3: a > -1
                    . simp at ha1
                      have : a < 3 := by exact lt_of_le_of_ne ha1 ha2
                      nlinarith
                    . by_cases ha4: a = -1
                      . left; linarith
                      . simp at ha3
                        have : a < -1 := by exact lt_of_le_of_ne ha3 ha4
                        cases ha
                        . linarith
                        . linarith
              . right;right; simp; linarith
            . exact hx1
          . intro hx
            rcases hx with rfl | rfl | rfl
            . simp
              ring_nf
              field_simp
            . simp
              ring_nf
              field_simp
            . simp
              ring_nf
              field_simp
              have : (2*a-3)*(2*a+1) ≥ 0 := by
                cases ha
                . nlinarith
                . nlinarith

              ring_nf at this
              nlinarith
