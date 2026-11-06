import Mathlib

set_option maxHeartbeats 4000000

/- 98. Prove: For any positive real numbers $a, b, c, d$, we have $\frac{(a-b)(a-c)}{a+b+c}+$ $\frac{(b-c)(b-d)}{b+c+d}+\frac{(c-d)(c-a)}{c+d+a}+\frac{(d-a)(d-b)}{d+a+b} \geqslant 0$, and determine the conditions for equality. (49th IMO Shortlist) -/
theorem inequalities_599966 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
  (a - b) * (a - c) / (a + b + c) + (b - c) * (b - d) / (b + c + d) +
  (c - d) * (c - a) / (c + d + a) + (d - a) * (d - b) / (d + a + b) ≥ 0 ∧
  ((a - b) * (a - c) / (a + b + c) + (b - c) * (b - d) / (b + c + d) +
  (c - d) * (c - a) / (c + d + a) + (d - a) * (d - b) / (d + a + b) = 0 ↔ a = c ∧ b = d) := by
  -- Let A, B, C, D be the four terms of the sum.
  let A := (a - b) * (a - c) / (a + b + c)
  let B := (b - c) * (b - d) / (b + c + d)
  let C := (c - d) * (c - a) / (c + d + a)
  let D := (d - a) * (d - b) / (d + a + b)
  -- We split each term X into two parts, X' and X''. The X' terms are squares, ensuring they are non-negative.
  let A' := (a - c) ^ 2 / (a + b + c)
  let B' := (b - d) ^ 2 / (b + c + d)
  let C' := (c - a) ^ 2 / (c + d + a)
  let D' := (d - b) ^ 2 / (d + a + b)
  -- The X'' terms are the remaining parts.
  let A'' := (a - c) * (a - 2 * b + c) / (a + b + c)
  let B'' := (b - d) * (b - 2 * c + d) / (b + c + d)
  let C'' := (c - a) * (c - 2 * d + a) / (c + d + a)
  let D'' := (d - b) * (d - 2 * a + b) / (d + a + b)
  -- We show that 2*X = X' + X'' for each term.
  have hA : 2 * A = A' + A'' := by
    field_simp [A, A', A'']
    ring
  have hB : 2 * B = B' + B'' := by
    field_simp [B, B', B'']
    ring
  have hC : 2 * C = C' + C'' := by
    field_simp [C, C', C'']
    ring
  have hD : 2 * D = D' + D'' := by
    field_simp [D, D', D'']
    ring
  -- Let s be the sum of a, b, c, d.
  let s := a + b + c + d
  -- This is a technical step using the Cauchy-Schwarz inequality.
  -- It sets up a lower bound for the sum of the squared terms (A' + B' + C' + D').
  have h1 : (|a - c| / √(s - d) * √(s - d) + |b - d| / √(s - a) * √(s - a) +
    |c - a| / √(s - b) * √(s - b) + |d - b| / √(s - c) * √(s - c)) ^ 2 ≤ 3 * s * (A' + B' + C' + D')
    := by
    let f : Fin 4 → ℝ := fun i => match i with
      | 0 => |a - c| / √(s - d)
      | 1 => |b - d| / √(s - a)
      | 2 => |c - a| / √(s - b)
      | 3 => |d - b| / √(s - c)
    let g : Fin 4 → ℝ := fun i => match i with
      | 0 => √(s - d)
      | 1 => √(s - a)
      | 2 => √(s - b)
      | 3 => √(s - c)
    calc
    _ = (∑ i, f i * g i) ^ 2 := by
      congr 1
      exact Eq.symm (Fin.sum_univ_four fun i => f i * g i)
    -- Apply Cauchy-Schwarz inequality.
    _ ≤ ((|a - c| / √(s - d)) ^ 2 + (|b - d| / √(s - a)) ^ 2 + (|c - a| / √(s - b)) ^ 2 +
      (|d - b| / √(s - c)) ^ 2) * ((√(s - d)) ^ 2 + (√(s - a)) ^ 2 + (√(s - b)) ^ 2 +
      (√(s - c)) ^ 2) := by
      rw [← Fin.sum_univ_four (fun i => f i ^ 2), ← Fin.sum_univ_four (fun i => g i ^ 2)]
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
    -- Simplify the expression.
    _ = 3 * s * (A' + B' + C' + D') := by
      simp [div_pow, Real.sq_sqrt (x := s - d) (by simp [s]; positivity),
        Real.sq_sqrt (x := s - a) (by simp [s]; linarith), Real.sq_sqrt (x := s - b)
        (by simp [s]; linarith), Real.sq_sqrt (x := s - c) (by simp [s]; linarith)]
      ring
  -- Simplify the left side of h1.
  rw [div_mul_cancel₀ _ (by simp [s]; positivity),
    div_mul_cancel₀ _ (by simp [s]; ring_nf; positivity),
    div_mul_cancel₀ _ (by simp [s]; ring_nf; positivity),
    div_mul_cancel₀ _ (by simp [s]; ring_nf; positivity)] at h1
  -- Establish a lower bound for the sum of squared terms using the result from h1 and AM-GM.
  have h2 : A' + B' + C' + D' ≥ 16 * |a - c| * |b - d| / (3 * s) := by
    trans (2 * |a - c| + 2 * |b - d|) ^ 2 / (3 * s)
    · simp
      rw [div_le_iff₀ (by positivity)]
      rw [show |c - a| = |a - c| by exact abs_sub_comm c a,
        show |d - b| = |b - d| by exact abs_sub_comm d b] at h1
      rw [two_mul, two_mul]
      linarith
    · simp
      -- Use the inequality (x+y)^2 >= 4xy.
      rw [div_le_div_iff₀ (by positivity) (by positivity), ← mul_add, mul_pow]
      suffices 4 * |a - c| * |b - d| ≤ (|a - c| + |b - d|) ^ 2 by
        apply mul_le_mul ?_ (by rfl) (by positivity) (by positivity)
        linarith
      exact four_mul_le_pow_two_add |a - c| |b - d|
  -- Define helper variables for algebraic manipulation.
  let M := s * (a + c) + b * d
  let N := s * (b + d) + a * c
  -- Simplify the sum of A'' and C''.
  have h3 : A'' + C'' = 3 * (a - c) * (d - b) * (a + c) / M := by
    field_simp [A'', C'']
    ring
  -- Simplify the sum of B'' and D''.
  have h4 : B'' + D'' = 3 * (b - d) * (a - c) * (b + d) / N := by
    field_simp [B'', D'']
    ring
  -- Define more helper variables.
  let W := b * d * (b + d) - a * c * (a + c)
  have hW : W = (b + d) * M - (a + c) * N := by ring
  -- Prove a necessary inequality for the next step.
  have hMN : M * N > |W| * s := by
    simp [M, N]
    apply lt_of_le_of_lt (b := (a * c * (a + c) + b * d * (b + d)) * s)
    · simp [W]
      apply mul_le_mul _ (by rfl) (by positivity) (by positivity)
      nth_rw 2 [← abs_of_nonneg (a := a * c * (a + c)) (by positivity),
        ← abs_of_nonneg (a := b * d * (b + d)) (by positivity)]
      nth_rw 3 [add_comm]
      exact abs_sub _ _
    · simp [mul_add, add_mul, ← mul_assoc, ← add_assoc, ← sub_pos]
      ring_nf
      positivity
  -- Establish an upper bound on the absolute value of the sum of the X'' terms.
  have h5 : |A'' + C'' + B'' + D''| ≤ 3 * |a - c| * |b - d| / s := by
    suffices A'' + C'' + B'' + D'' = 3 * (a - c) * (b - d) * W / (M * N) by
      simp [this, abs_div, abs_mul]
      rw [← mul_one_div (y := s), ← mul_div]
      apply mul_le_mul (by rfl) _ (by positivity) (by positivity)
      rw [div_le_div_iff₀ (by positivity) (by positivity),
        abs_of_nonneg (a := M) (by positivity), abs_of_nonneg (a := N) (by positivity)]
      linarith
    rw [h3, add_assoc, h4, hW]
    field_simp
    ring
  -- Simple rearrangement of terms.
  have g1 : A' + A'' + (B' + B'') + (C' + C'') + (D' + D'') =
      (A' + B' + C' + D') + (A'' + C'' + B'' + D'') := by ring
  -- This means A'' + C'' + B'' + D'' >= -3 * |a-c|*|b-d| / s
  have h5 := abs_le.1 h5 |>.1
  -- Combine the lower bound for X' sum (h2) and the lower bound for X'' sum (h5)
  -- to get a lower bound for the total expression 2*(A+B+C+D).
  have h6 : 2 * (A + B + C + D) ≥ 7 * |a - c| * |b - d| / (3 * s) := by
    simp [mul_add, hA, hB, hC, hD, g1]
    suffices 7 * |a - c| * |b - d| / (3 * s)= 16 * |a - c| * |b - d| / (3 * s) +
      -(3 * |a - c| * |b - d| / s) by
      linarith
    field_simp [← sub_eq_add_neg, ← mul_assoc]
    left
    ring
  -- The proof is split into two goals: the inequality and the equality condition.
  constructor
  -- First goal: prove the inequality is non-negative.
  · simp
    rw [← mul_nonneg_iff_right_nonneg_of_pos (a := 2) (by norm_num)]
    change 0 ≤ 2 * (A + B + C + D)
    trans 7 * |a - c| * |b - d| / (3 * s)
    · -- The RHS of h6 is non-negative.
      positivity
    · -- The main expression is greater than or equal to the RHS of h6.
      exact h6
  -- Second goal: prove the equality condition (if and only if).
  · constructor
    -- First direction: if the sum is 0, then a=c and b=d.
    · intro h
      -- If the sum is 0, the lower bound in h6 must be <= 0.
      simp [h] at h6
      have h7 : 7 * |a - c| * |b - d| / (3 * s) = 0 := by
        suffices 7 * |a - c| * |b - d| / (3 * s) ≥ 0 by linarith
        positivity
      -- For the fraction to be 0, the numerator must be 0.
      rw [div_eq_zero_iff] at h7
      rcases h7 with h7 | h7
      -- This implies |a-c|=0 or |b-d|=0.
      · simp [sub_eq_zero] at h7
        rcases h7 with h7 | h7
        -- Case 1: a = c. We must show b = d.
        · suffices b = d by exact ⟨h7, this⟩
          -- Assume b != d for contradiction.
          by_contra! hbd
          have h8 : (b - d) ^ 2 / (b + c + d) + (d - b) ^ 2 / (d + c + b) > 0 := by
            suffices (b - d) ^ 2 > 0 by positivity
            apply pow_two_pos_of_ne_zero (by exact sub_ne_zero_of_ne hbd)
          -- This would imply a strict inequality in h2.
          have h9 : A' + B' + C' + D' > 16 * |a - c| * |b - d| / (3 * s) := by
            simp [h7, A', B', C', D', h8]
          change A + B + C + D = 0 at h
          apply mul_eq_zero_of_right (a := 2) at h
          -- And thus a strict inequality in h6.
          have h6 : 2 * (A + B + C + D) > 7 * |a - c| * |b - d| / (3 * s) := by
            simp [mul_add, hA, hB, hC, hD, g1]
            suffices 7 * |a - c| * |b - d| / (3 * s)= 16 * |a - c| * |b - d| / (3 * s) +
              -(3 * |a - c| * |b - d| / s) by
              linarith
            field_simp [← sub_eq_add_neg, ← mul_assoc]
            left
            ring
          -- This leads to 0 > 0, a contradiction.
          simp [h] at h6
          rw [div_lt_iff₀ (by positivity)] at h6
          suffices 7 * |a - c| * |b - d| ≥ 0 by linarith
          positivity
        -- Case 2: b = d. We must show a = c. The logic is symmetric to Case 1.
        · suffices a = c by exact ⟨this, h7⟩
          by_contra! hac
          have h8 : (a - c) ^ 2 / (a + d + c) + (c - a) ^ 2 / (c + d + a) > 0 := by
            suffices (a - c) ^ 2 > 0 by positivity
            apply pow_two_pos_of_ne_zero (by exact sub_ne_zero_of_ne hac)
          have h9 : A' + B' + C' + D' > 16 * |a - c| * |b - d| / (3 * s) := by
            simp [h7, A', B', C', D', h8]
          change A + B + C + D = 0 at h
          apply mul_eq_zero_of_right (a := 2) at h
          have h6 : 2 * (A + B + C + D) > 7 * |a - c| * |b - d| / (3 * s) := by
            simp [mul_add, hA, hB, hC, hD, g1]
            suffices 7 * |a - c| * |b - d| / (3 * s)= 16 * |a - c| * |b - d| / (3 * s) +
              -(3 * |a - c| * |b - d| / s) by
              linarith
            field_simp [← sub_eq_add_neg, ← mul_assoc]
            left
            ring
          simp [h] at h6
          rw [div_lt_iff₀ (by positivity)] at h6
          suffices 7 * |a - c| * |b - d| ≥ 0 by linarith
          positivity
      -- The denominator cannot be zero.
      · simp [s] at h7
        linarith
    -- Second direction: if a=c and b=d, then the sum is 0.
    · rintro ⟨rfl, rfl⟩
      -- This is straightforward by substitution.
      simp