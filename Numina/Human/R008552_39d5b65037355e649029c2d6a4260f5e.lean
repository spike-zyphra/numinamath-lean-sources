import Mathlib

/- Find all real numbers $x$ such that \[
x^2 + \left\lfloor \frac x2 \right\rfloor + \left\lfloor \frac x3
\right\rfloor = 10.
\]Enter all the solutions, separated by commas. -/
theorem algebra_21631 (x : ℝ) :
    x^2 + ⌊x / 2⌋ + ⌊x / 3⌋ = 10 ↔ x = -√14 := by
  -- Two goals to prove
  -- 1. If x^2 + ⌊x / 2⌋ + ⌊x / 3⌋ = 10, then x = -√14
  -- 2. If x = -√14, then x^2 + ⌊x / 2⌋ + ⌊x / 3⌋ = 10
  constructor
  . -- First goal
    intro h
    -- x^2 is an integer n, and n + ⌊x / 2⌋ + ⌊x / 3⌋ = 10
    have ⟨n, H1, H2⟩ : ∃ n : ℤ, x^2 = n ∧ n + ⌊x / 2⌋ + ⌊x / 3⌋ = 10 := by
      -- Clear from the hypothesis
      use 10 - ⌊x / 2⌋ - ⌊x / 3⌋
      simp
      constructor
      . linear_combination h
      . ring
    -- x cannot be 0
    have hx' : x ≠ 0 := by
      rintro rfl
      simp at h
    -- So x < 0 or x > 0
    rcases lt_or_gt_of_ne hx' with hx | hx
    . -- Assume x < 0
      -- We get ⌊x / 2⌋ < 0 and ⌊x / 3⌋ < 0
      have h1 : ⌊x / 2⌋ < 0 := Int.floor_lt.2 (by simp; linarith)
      have h2 : ⌊x / 3⌋ < 0 := Int.floor_lt.2 (by simp; linarith)
      -- Then n = 10 - ⌊x / 2⌋ - ⌊x / 3⌋ ≥ 12
      have h3 : n ≥ 12 := by omega
      -- We prove n < 16 by contradiction
      have h4 : n < 16 := by
        by_contra! k
        clear hx' h1 h2 h3
        -- 10 = x^2 + ⌊x / 2⌋ + ⌊x / 3⌋ > x^2 + (x / 2 - 1) + (x / 3 - 1)
        replace h : 10 > x^2 + (x / 2 - 1) + (x / 3 - 1) :=
          calc _ = x^2 + ⌊x / 2⌋ + ⌊x / 3⌋ := by rw [h]
               _ > x^2 + (x / 2 - 1) + (x / 3 - 1) := by linarith [Int.sub_one_lt_floor (x / 2), Int.sub_one_lt_floor (x / 3)]
        replace h : x^2 + 5 * x / 6 < 12 := by linarith
        -- x ≤ -4 from n ≥ 16
        have h1 : x ≤ -4 := by
          suffices h1 : x^2 ≥ 16 by nlinarith
          rw [H1]
          norm_cast
        -- The quadratic inequality x^2 + 5 * x / 6 < 12 is not satisfied
        nlinarith
      -- x = -√(x^2) because x < 0
      have h0 : x = -√(x ^ 2) :=
        calc x = -(-x) := by simp
             _ = -√((-x)^2) := by rw [Real.sqrt_sq (by linarith)]
             _ = -√(x^2) := by simp
      -- n = 12, 13, 14, 15
      interval_cases n
      -- Simplify the goals
      all_goals
        clear hx' h1 h2 h3 h4
        norm_cast at H1
        rw [H1] at h0
        subst x
        clear * - H2
      -- Check the cases one by one
      . have h1 : 3 < √12 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
        have h2 : √12 < 4 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
        have K1 : ⌊-√12 / 2⌋ = -2 := by
          rw [Int.floor_eq_iff]
          norm_num
          constructor <;> linarith
        have K2 : ⌊-√12 / 3⌋ = -2 := by
          rw [Int.floor_eq_iff]
          norm_num
          constructor <;> linarith
        rw [K1, K2] at H2
        norm_num at H2
      . have h1 : 3 < √13 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
        have h2 : √13 < 4 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
        have K1 : ⌊-√13 / 2⌋ = -2 := by
          rw [Int.floor_eq_iff]
          norm_num
          constructor <;> linarith
        have K2 : ⌊-√13 / 3⌋ = -2 := by
          rw [Int.floor_eq_iff]
          norm_num
          constructor <;> linarith
        rw [K1, K2] at H2
        norm_num at H2
      . rfl
      . have h1 : 3 < √15 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
        have h2 : √15 < 4 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
        have K1 : ⌊-√15 / 2⌋ = -2 := by
          rw [Int.floor_eq_iff]
          norm_num
          constructor <;> linarith
        have K2 : ⌊-√15 / 3⌋ = -2 := by
          rw [Int.floor_eq_iff]
          norm_num
          constructor <;> linarith
        rw [K1, K2] at H2
        norm_num at H2
    . -- Assume x > 0
      clear hx'
      exfalso
      -- f(x) = x^2 + ⌊x / 2⌋ + ⌊x / 3⌋ is monotone increasing on (0, ∞)
      let f (x : ℝ) := x ^ 2 + ↑⌊x / 2⌋ + ↑⌊x / 3⌋
      have H : MonotoneOn f {x | x > 0} := by
        intro x hx y hy hxy
        simp at hx hy
        simp [f]
        -- Each term is increasing
        have h1 : x ^ 2 ≤ y ^ 2 := by nlinarith
        have h2 : (⌊x / 2⌋ : ℝ) ≤ ⌊y / 2⌋ := by
          norm_cast
          apply Int.floor_mono
          linarith
        have h3 : (⌊x / 3⌋ : ℝ) ≤ ⌊y / 3⌋ := by
          norm_cast
          apply Int.floor_mono
          linarith
        linarith
      -- f(√8) < 10
      have K1 :f √8 < 10 := by
        simp [f]
        have h1 : 2 < √8 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
        have h2 : √8 < 3 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
        have h3 : ⌊√8 / 2⌋ = 1 := by
          rw [Int.floor_eq_iff]
          norm_num
          constructor <;> linarith
        have h4 : ⌊√8 / 3⌋ = 0 := by
          rw [Int.floor_eq_iff]
          norm_num
          constructor <;> linarith
        rw [h3, h4]
        norm_num
      -- f(3) > 10
      have K2 : f 3 > 10 := by
        simp [f]
        norm_num
      -- f(x) = 10
      change f x = 10 at h
      -- x > √8 and x < 3 from monotonicity
      have h1 : x > √8 := by
        by_contra! k
        have h1 : f x ≤ f √8 := H hx (show √8 > 0 by positivity) k
        linarith
      have h2 : x < 3 := by
        by_contra! k
        have h1 : f 3 ≤ f x := H (show (3 : ℝ) > 0 by positivity) hx k
        linarith
      -- x^2 > 8 and x^2 < 9
      replace h1 : x^2 > 8 := (Real.sqrt_lt' hx).1 h1
      replace h2 : x^2 < 9 := by nlinarith
      -- n > 8 and n < 9
      rw [H1] at h1 h2
      norm_cast at h1 h2
      -- Which is impossible
      interval_cases n
  . -- Second goal
    -- Check the case x = -√14
    rintro rfl
    simp
    have h1 : 3 < √14 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
    have h2 : √14 < 4 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have K1 : ⌊-√14 / 2⌋ = -2 := by
      rw [Int.floor_eq_iff]
      norm_num
      constructor <;> linarith
    have K2 : ⌊-√14 / 3⌋ = -2 := by
      rw [Int.floor_eq_iff]
      norm_num
      constructor <;> linarith
    rw [K1, K2]
    norm_num
