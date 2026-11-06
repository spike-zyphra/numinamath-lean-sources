import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/- Determine all pairs of integers  $(a, b)$   that solve the equation  $a^3 + b^3 + 3ab = 1$ .-/
theorem number_theory_8537 (a b : ℤ) :
  a^3 + b^3 + 3 * a * b = 1 ↔ a = -1 ∧ b = -1 ∨ a + b = 1:= by
    -- An auxiliary lemma :
    -- \[
    -- a^3 + b^3 + c^3 - 3abc = (a + b + c)(a^2 + b^2 + c^2 - ab - ac - bc)
    -- \]
    have aux (a b c : ℤ) : a^3 + b^3 + c^3 = 3 * a * b * c +
      (a + b + c) * (a^2 + b^2 + c^2 - a*b - a*c - b*c) := by nlinarith
    constructor <;> intro h
    · -- To fit our equation into this identity, let’s set \(c = -1\). Substituting, we get:
      -- \[
      -- a^3 + b^3 + (-1)^3 - 3ab(-1) = (a + b - 1)(a^2 + b^2 + 1 - ab + a + b) = 0
      -- \]
      have h1 := aux a b (-1)
      simp at h1
      have : (a + b + -1) * (a ^ 2 + b ^ 2 + 1 - a * b + a + b) = 0 := calc
        _ = a^3 + b^3 + 3 * a * b - 1 := by linarith
        _ = _ := by apply sub_eq_of_eq_add; linarith
      -- This implies two cases: Case 1: \(a + b - 1 = 0\), i.e. $a + b = 1$.
      simp at this
      rcases this with hl | hr
      · right; linarith
      · -- Case 2:** \(a^2 + b^2 + 1 - ab + a + b = 0\)
        left
        -- Using the basic inequality we get that $(a + 1) * (b + 1) \leq 0$.
        have h2 : (a + 1) * (b + 1) ≤ 0 := calc
          _ = 2 * a * b + 1 - a * b + a + b := by linarith
          _ ≤ a ^ 2 + b ^ 2 + 1 - a * b + a + b := by
            rw [show a ^ 2 + b ^ 2 + 1 - a * b + a + b = (a ^ 2 + b ^ 2) + (1 - a * b + a + b) by ring]
            rw [show 2 * a * b + 1 - a * b + a + b = 2 * a * b + (1 - a * b + a + b) by ring]
            exact _root_.add_le_add (two_mul_le_add_pow_two a b) le_rfl
          _ = _ := hr
        -- In addition, from $(a^2 + b^2 + 1 - ab + a + b) = 0$ we can obtain $0 < ab$.
        have h3 : 0 < a * b := by
          by_contra! nonpos
          by_cases ab0 : a * b = 0
          · simp at ab0
            rcases ab0 with h0 | h0 <;> simp [h0] at hr <;> nlinarith
          · have abneg : a * b < 0 := by omega
            nlinarith
        have same_pairty : 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 :=
          pos_and_pos_or_neg_and_neg_of_mul_pos h3
        -- Under these conditions, only both $a$ and $b$ negative is possible.
        have both_neg : a < 0 ∧ b < 0 :=
          (or_iff_right (by simp; intro apos; linarith)).1 same_pairty
        -- So we also get $0 ≤ (a + 1) * (b + 1)$, implies $(a + 1) * (b + 1) = 0$, i.e.
        -- $a + 1 = 0$ or $b + 1 = 0$.
        have h4 : a + 1 = 0 ∨ b + 1 = 0 := by
          have : a + 1 ≤ 0 ∧ b + 1 ≤ 0 := by omega
          have : 0 ≤ (a + 1) * (b + 1) := Int.mul_nonneg_iff.2 (Or.inr ⟨this.1, this.2⟩)
          have : (a + 1) * (b + 1) = 0 := by omega
          exact Int.mul_eq_zero.1 this
        -- both above cases imply $a = b = -1$.
        rcases h4 with h4 | h4
        · exact ⟨by omega, by nlinarith⟩
        · exact ⟨by nlinarith, by omega⟩
    · -- Verify the necessity.
      rcases h with hl | hr
      · simp [hl]
      · have : a = 1 - b := by omega
        simp [this]
        ring_nf
