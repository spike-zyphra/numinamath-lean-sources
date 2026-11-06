import Mathlib

/-
5. The side-lengths $a, b, c$ of a triangle $A B C$ are positive integers. Let


$$

T_{n}=(a+b+c)^{2 n}-(a-b+c)^{2 n}-(a+b-c)^{2 n}+(a-b-c)^{2 n}

$$


for any positive integer $n$. If $\frac{T_{2}}{2 T_{1}}=2023$ and $a>b>c$, determine all possible perimeters of the triangle $A B C$.

 -/
theorem algebra_123213 (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hnondeg : a < b + c)
    (h : a > b ∧ b > c) (T : ℕ → ℤ) (hT : ∀ n, T n = (a + b + c) ^ (2 * n) -
    (a - b + c) ^ (2 * n) - (a + b - c) ^ (2 * n) + (a - b - c) ^ (2 * n))
    (hT1 : T 1 ≠ 0) (hT2 : T 2 ≠ 0) (hT3 : T 2 / (2 * T 1) = 2023) :
    a + b + c = 49 := by
-- First, we compute explicit formulae for T 1 and T 2 in terms of a,b,c.
      have hT1 : T 1 = 8*b*c := by
        rw [hT 1]
        ring_nf
      have hT2 : T 2 = 16*b*c*(3*a^2 + b^2 + c^2) := by
        rw [hT 2]
        ring_nf
-- We obtain the equation 3a^2+b^2+c^2=2023 from the given condition.
      rw [hT1, hT2] at hT3
      have : (16 * b * c * (3 * a ^ 2 + b ^ 2 + c ^ 2) / (2 * (8 * b * c))) = (16 * b * c) * (3 * a ^ 2 + b ^ 2 + c ^ 2) / (16 * b * c) := by ring_nf
      rw [this] at hT3
      have : (16 * b * c) * (3 * a ^ 2 + b ^ 2 + c ^ 2) / (16 * b * c) = (3 * a ^ 2 + b ^ 2 + c ^ 2) := by field_simp
      rw [this] at hT3
-- We prove that a cannot be even, since otherwise the equation modulo 4 would not have a solution.
      have aeven : ¬ Even a := by
        intro h
        have : (b : ZMod 4) ^ 2 + c ^ 2 = 2023 - 3 * a ^ 2 := by
          rw_mod_cast [← hT3]
          ring_nf
        have eqmod4 : (b : ZMod 4) ^ 2 + c ^ 2 = 3 := by
          rw [this]
          have : (2023 : ZMod 4) = 3 := by
            decide
          rw [this]
          have : (a ^ 2 : ZMod 4) = 0 := by
            rw [even_iff_two_dvd] at h
            obtain ⟨k, hk⟩ := h
            rw_mod_cast [hk, mul_pow]
            simp only [Int.reducePow, Int.cast_mul, Int.cast_ofNat, Int.cast_pow]
            have : (4 : ZMod 4) = 0 := by
              decide
            rw [this]
            simp only [zero_mul]
          rw [this]
          simp
        have (x : ℤ) : (x : ZMod 4) ^ 2 = 0 ∨ (x : ZMod 4) ^ 2 = 1 := by
          have hx := Int.even_or_odd' x
          obtain ⟨k, hk⟩ := hx
          rcases hk with hk | hk
          · left
            rw_mod_cast [hk, mul_pow]
            simp only [Int.reducePow, Int.cast_mul, Int.cast_ofNat, Int.cast_pow]
            have : (4 : ZMod 4) = 0 := by
              decide
            rw [this]
            simp only [zero_mul]
          · right
            rw_mod_cast [hk]
            ring_nf
            have : (4 : ZMod 4) = 0 := by
              decide
            simp [this]
        have bsq := this b
        have csq := this c
        rcases bsq with bsq | bsq
        · rcases csq with csq | csq
          · exfalso
            rw [bsq, csq] at eqmod4
            contradiction
          · exfalso
            rw [bsq, csq] at eqmod4
            contradiction
        · rcases csq with csq | csq
          · exfalso
            rw [bsq, csq] at eqmod4
            contradiction
          · exfalso
            rw [bsq, csq] at eqmod4
            contradiction
-- We find a lower bound for a^2, using that a > b > c.
      have : 3 * a ^ 2 + b ^ 2 + c ^ 2 < 5 * a ^ 2 := by
        have : b ^ 2 < a ^ 2 := by
          rw [sq_lt_sq]
          have : |b| = b := abs_of_pos hb
          rw [this]
          have : |a| = a := abs_of_pos ha
          rw [this]
          exact h.1
        have : c ^ 2 < a ^ 2 := by
          apply lt_trans _ this
          rw [sq_lt_sq]
          have : |c| = c := abs_of_pos hc
          rw [this]
          have : |b| = b := abs_of_pos hb
          rw [this]
          exact h.2
        linarith
      rw [hT3] at this
-- We obtain a^2 ≥ 404.
      have h404 : a ^ 2 ≥ 404 := by linarith
-- We find an upper bound for a^2, using that b^2 + c^2 > 0.
      have : 3 * a ^ 2 < 2023 := by
        rw [← hT3]
        rw [add_assoc]
        simp only [lt_add_iff_pos_right]
        positivity
-- We obtain a^2 ≤ 675.
      have h675 : a ^ 2 ≤ 675 := by linarith
-- Using the fact that a is a positive integer, we prove that a is bounded between 21 and 25.
      have bound_a : 21 ≤ a ∧ a ≤ 25 := by
        constructor
        · rw [(by norm_num : (21 : ℤ)= 20 + 1), Int.add_one_le_iff]
          have : |a| = a := by
            apply abs_of_pos
            exact ha
          rw [(by norm_num : (20 : ℤ) = |20|), ← this, ← sq_lt_sq]
          linarith
        · have : a ≤ 25 ↔ a < 26 := by
            rw [← Int.lt_add_one_iff]
            norm_num
          rw [this]
          have : |a| = a := by
            apply abs_of_pos
            exact ha
          rw [(by norm_num : (26 : ℤ) = |26|), ← this, ← sq_lt_sq]
          linarith
      obtain ⟨a21, a25⟩ := bound_a
-- We conclude that a can either be 21, 23, or 25, since it is odd.
      have possible_a : a = 21 ∨ a = 23 ∨ a = 25 := by
        interval_cases a
        · left; rfl
        · contradiction
        · right; left; rfl
        · contradiction
        · right; right; rfl
-- We consider all possible values for a and thus b and c, knowing that a > b > c.
      rcases possible_a with a21 | a23 | a25
-- If we assume a = 21, there are no b and c satifying the equation.
      · exfalso
        rw [a21] at h hT3
        ring_nf at hT3
        have eqbc : b ^ 2 + c ^ 2 = 700 := by
          rw [(by norm_num : (700 : ℤ) = 2023 - 1323)]
          rw [← hT3]
          ring_nf
        have : b < 21 := h.1
        have : c < 21 := by
          apply lt_trans h.2 this
        interval_cases b
        all_goals {
          interval_cases c
          all_goals {
            norm_num at eqbc
          }
        }
-- If we assume a = 23, then b = 20 and c = 6 satisfy the equation and the given conditions.
      · rw [a23] at h hT3 ⊢
        ring_nf at hT3
        have eqbc : b ^ 2 + c ^ 2 = 436 := by
          rw [(by norm_num : (436 : ℤ) = 2023 - 1587)]
          rw [← hT3]
          ring_nf
        have : b < 23 := h.1
        have : c < 23 := by
          apply lt_trans h.2 this
        interval_cases b
        all_goals {
          interval_cases c
          all_goals {
            norm_num at eqbc ⊢
          }
        }
-- If we assume a = 25, then the only values of b and c satifying the equation correspond to a degenerate triangle, so there are no new solutions.
      · rw [a25] at h hT3 hnondeg
        ring_nf at hT3
        have eqbc : b ^ 2 + c ^ 2 = 148 := by
          rw [(by norm_num : (148 : ℤ) = 2023 - 1875)]
          rw [← hT3]
          ring_nf
        have : b < 25 := h.1
        have : c < 25 := by
          apply lt_trans h.2 this
        interval_cases b
        all_goals {
          interval_cases c
          all_goals {
            norm_num at eqbc hnondeg ⊢
          }
        }