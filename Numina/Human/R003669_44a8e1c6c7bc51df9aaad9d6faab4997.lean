import Mathlib

open Real Set

/- 1. Solve the inequality $\operatorname{tg} \arccos x \leqslant \sin \operatorname{arctg} x$. Answer: $\left[-\frac{1}{\sqrt[4]{2}} ; 0\right) \cup\left[\frac{1}{\sqrt[4]{2}} ; 1\right]$. -/
theorem inequalities_205694 (x : ℝ) (hx : x ∈ Icc (-1) 1) (hx0 : x ≠ 0) :
    tan (arccos x) ≤ sin (arctan x) ↔
    x ∈ Ico (-1 / (2 ^ (1 / 4 : ℝ))) 0 ∪ Icc (1 / (2 ^ (1 / 4 : ℝ))) 1 := by
  have hineq : 0 ≤ 1 / (2 : ℝ)^(1 / 4 : ℝ) := by positivity
  simp only [mem_Icc] at hx
  -- We have tan (arccos x) = √(1 - x^2) / x and
  -- sin (arctan x) = x / √(1 + x^2).
  rw [tan_arccos, sin_arctan]
  -- Consider two cases: x < 0 or x > 0.
  by_cases hx1 : x < 0
  · calc
      -- If x < 0 then rewrite the inequality as:
      -- (-x) / √(1 + x^2) ≤ √(1 - x^2) / (-x).
      _ ↔ (-x) / √(1 + x^2) ≤ √(1 - x^2) / (-x) := by
        rw [neg_div, div_neg, neg_le_neg_iff]
      -- (-x) * (-x) ≤ √(1 + x^2) * √(1 - x^2) ↔ x^2 ≤ √(1 - x^4).
      _ ↔ x * x ≤ √(1 - x^4) := by
        rw [div_le_div_iff₀ (by positivity) (by linarith)]
        rw [← sqrt_mul (by nlinarith)]
        ring_nf
      -- We get x^4 ≤ 1 - x^4.
      _ ↔ x^4 ≤ 1 - x^4 := by
        rw [← sq_le_sq₀ (by nlinarith) (by positivity)]
        rw [sq_sqrt]
        · ring_nf
        · rw [sub_nonneg, show x^4 = (x^2)^2 by ring, show (1 : ℝ) = (1^2)^2 by norm_num]
          rw [sq_le_sq, abs_pow, abs_pow, sq_le_sq]
          simp only [abs_abs, abs_one, abs_le, hx, and_true]
      -- We get (x^2)^2 ≤ 1/2.
      _ ↔ (x^2)^2 ≤ 1 / 2 := by
        simp [← pow_mul]
        constructor <;> (intros; linarith)
      -- We get (x^2)^2 ≤ ((1/2^(1/4))^2)^2.
      _ ↔ (x^2)^2 ≤ ((1 / 2 ^ (1 / 4 : ℝ))^2)^2 := by
        conv =>
          rhs; rhs
          rw [← pow_mul, div_pow, one_pow, ← rpow_natCast, ← rpow_mul (by norm_num)]
        norm_num
      -- We obtain |x| ≤ 1/2^(1/4).
      -- x < 0 implies -1/2^(1/4) ≤ x < 0.
      _ ↔ x ∈ Ico (-1 / 2 ^ (1 / 4 : ℝ)) 0 := by
        rw [sq_le_sq, abs_pow, abs_pow, sq_le_sq, abs_abs, abs_of_neg hx1, abs_abs, abs_of_nonneg hineq]
        rw [mem_Ico, neg_div]
        constructor
        · intro h
          constructor <;> linarith
        · intro h
          linarith
      -- x < 0 so x ∈ [-1/2^(1/4), 0) ↔ x ∈ [-1/2^(1/4), 0) ∪ [1/2^(1/4), 1].
      _ ↔ x ∈ Ico (-1 / (2 ^ (1 / 4 : ℝ))) 0 ∪ Icc (1 / (2 ^ (1 / 4 : ℝ))) 1 := by
        constructor
        · intro h
          left
          exact h
        · intro h
          cases' h with h h
          · exact h
          · simp only [mem_Icc] at h
            linarith
  · -- Consider the case 0 < x.
    replace hx1 : 0 < x := by
      rw [lt_iff_le_and_ne]
      simp only [not_lt] at hx1
      exact ⟨hx1, hx0.symm⟩
    calc
      -- The inequality is equivalent to √(1 - x^4) ≤ x^2.
      _ ↔ √(1 - x^4) ≤ x * x := by
        rw [div_le_div_iff₀ hx1 (by positivity)]
        rw [← sqrt_mul (by nlinarith)]
        ring_nf
      _ ↔ 1 - x^4 ≤ x^4 := by
        rw [← sq_le_sq₀ (by positivity) (by nlinarith)]
        rw [sq_sqrt]
        · ring_nf
        · rw [sub_nonneg, show x^4 = (x^2)^2 by ring, show (1 : ℝ) = (1^2)^2 by norm_num]
          rw [sq_le_sq, abs_pow, abs_pow, sq_le_sq]
          simp only [abs_abs, abs_one, abs_le, hx, and_true]
      -- We get 1/2 ≤ x^4.
      _ ↔ 1 / 2 ≤ (x^2)^2 := by
        simp [← pow_mul]
        constructor <;> (intros; linarith)
      _ ↔ ((1 / 2 ^ (1 / 4 : ℝ))^2)^2 ≤ (x^2)^2 := by
        conv =>
          rhs; lhs
          rw [← pow_mul, div_pow, one_pow, ← rpow_natCast, ← rpow_mul (by norm_num)]
        norm_num
      -- ((1/2^(1/4))^2)^2 ≤ (x^2)^2 iff 1/2^(1/4) ≤ |x|.
      -- 0 < x implies that |x| = x and we get x ∈ [1/2^(1/4), 1].
      _ ↔ x ∈ Icc (1 / (2 ^ (1 / 4 : ℝ))) 1 := by
        rw [sq_le_sq, abs_pow, abs_pow, sq_le_sq]
        simp only [abs_abs, mem_Ico, abs_of_nonneg hineq, abs_of_pos hx1, mem_Icc]
        constructor <;> intros
        · constructor <;> linarith
        · linarith
      -- 0 < x implies that x ∈ [1/2^(1/4), 1] iff x ∈ [-1, -1/2^(1/4)) ∪ [1/2^(1/4), 1].
      _ ↔ x ∈ Ico (-1 / (2 ^ (1 / 4 : ℝ))) 0 ∪ Icc (1 / (2 ^ (1 / 4 : ℝ))) 1 := by
        constructor
        · intro h
          right
          exact h
        · intro h
          cases' h with h h
          · simp only [mem_Ico] at h
            linarith
          · exact h