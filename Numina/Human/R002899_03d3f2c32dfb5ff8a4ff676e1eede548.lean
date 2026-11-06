import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Tactic

/- 9th ASU 1975 Problem 8 a, b, c are positive reals. Show that a 3 + b 3 + c 3 + 3abc ≥ ab(a + b) + bc(b + c) + ca(c + a). -/
theorem inequalities_127821 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a^3 + b^3 + c^3 + 3 * a * b * c ≥ a * b * (a + b) + b * c * (b + c) + c * a * (c + a) := by

      --Following is a proof of Schur's lemma. We'll use it to prove our inequality.
      have schur {a b c r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hr : 0 < r) :
          0 ≤ a ^ r * (a - b) * (a - c) + b ^ r * (b - a) * (b - c) + c ^ r * (c - a) * (c - b) := by
        wlog hcb : c ≤ b generalizing a b c
        case inr => linarith [this ha hc hb (by linarith)]
        wlog hba : b ≤ a generalizing a b c
        case inr =>
          rcases le_total a c with hac | hca
          case inl => linarith [this hb hc ha hac hcb]
          case inr => linarith [this hb ha hc hca (by linarith)]
        have hcr : 0 ≤ c ^ r := Real.rpow_nonneg hc r
        have h₁ : 0 ≤ c ^ r * (c - a) * (c - b) := by
          rw [mul_assoc]
          exact mul_nonneg hcr (by nlinarith)
        have he : a ^ r * (a - b) * (a - c) + b ^ r * (b - a) * (b - c) =
            (a - b) * (a ^ r * (a - c) - b ^ r * (b - c)) := by
          ring
        rw [he]
        refine add_nonneg ?_ h₁
        refine mul_nonneg (by linarith) ?_
        rw [sub_nonneg]
        gcongr ?_ ^ _ * (?_ - _)
        linarith

      --We have the following conditions.
      have ha' : 0 ≤ a := by linarith
      have hb' : 0 ≤ b := by linarith
      have hc' : 0 ≤ c := by linarith
      have hr' : (0 : ℝ) < (1) := by norm_num

      --Use schur to show...
      have ineq' :  0 ≤ a^(1 : ℝ) * (a - b) * (a - c) + b^(1 : ℝ) * (b - a) * (b - c) + c^(1 : ℝ) * (c - a) * (c - b) := by
        have := schur ha' hb' hc' hr'
        simp only [Nat.cast_one] at this
        exact this

      --Show a^(1 : ℝ) * (a - b) * (a - c) + b^(1 : ℝ) * (b - a) * (b - c) + c^(1 : ℝ) * (c - a) * (c - b) = a * (a - b) * (a - c) + b * (b - a) * (b - c) + c * (c - a) * (c - b).
      have eq : a^(1 : ℝ) * (a - b) * (a - c) + b^(1 : ℝ) * (b - a) * (b - c) + c^(1 : ℝ) * (c - a) * (c - b) = a * (a - b) * (a - c) + b * (b - a) * (b - c) + c * (c - a) * (c - b) := by
        norm_cast
        simp [pow_one]

      --Show 0 ≤ a * (a - b) * (a - c) + b * (b - a) * (b - c) + c * (c - a) * (c - b).
      have ineq :  0 ≤ a * (a - b) * (a - c) + b * (b - a) * (b - c) + c * (c - a) * (c - b)  := by
        rw [←eq]
        exact schur ha' hb' hc' hr'

      --Show a^3 + b^3 + c^3 + 3 * a * b * c - (a * b * (a + b) + b * c * (b + c) + c * a * (c + a)) = a * (a - b) * (a - c) + b * (b - a) * (b - c) + c * (c - a) * (c - b).
      have eq' :  a^3 + b^3 + c^3 + 3 * a * b * c - (a * b * (a + b) + b * c * (b + c) + c * a * (c + a)) = a * (a - b) * (a - c) + b * (b - a) * (b - c) + c * (c - a) * (c - b) := by ring

      --Show a^3 + b^3 + c^3 + 3 * a * b * c - (a * b * (a + b) + b * c * (b + c) + c * a * (c + a)).
      have ineq' : a^3 + b^3 + c^3 + 3 * a * b * c - (a * b * (a + b) + b * c * (b + c) + c * a * (c + a)) ≥ 0 := by
        rw [eq']
        exact ineq

      --SHow a^3 + b^3 + c^3 + 3 * a * b * c ≥ a * b * (a + b) + b * c * (b + c) + c * a * (c + a).
      have ineq'' : a^3 + b^3 + c^3 + 3 * a * b * c ≥ a * b * (a + b) + b * c * (b + c) + c * a * (c + a) := by
        exact sub_nonneg.mp ineq'

      --Done.
      exact ineq''