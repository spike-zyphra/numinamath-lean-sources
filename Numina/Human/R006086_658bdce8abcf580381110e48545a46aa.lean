import Mathlib

open Real
/-Find all real numbers x such that
x ^ 2 + ⌊x / 2⌋ + ⌊x / 3⌋ = 10-/
theorem algebra_611482: {x: ℝ | x ^ 2 + ⌊x / 2⌋ + ⌊x / 3⌋ = 10} = {-√14} := by
  ext x
  constructor
  -- First, we show that if x is in the set, then it must be -√14.
  . intro h
    simp at *
    -- we first obtain two inequalities from the equation
    have ineq: x ^ 2 + 5 / 6 * x - 12 < 0 := by
      have h1: ↑⌊x / 2⌋ > x / 2 - 1 := by simp
      have h2: ↑⌊x / 3⌋ > x / 3 - 1 := by simp
      nlinarith [h1,h2,h]
    have hx1: x < 3.1 := by nlinarith
    have hx2: -4 < x := by nlinarith
     -- we then get another two inequalities from the equation
    have ineq2: 0 ≤ x ^ 2 + 5 / 6 * x - 10 := by
      have h1: ⌊x / 2⌋ ≤ x / 2 := by apply Int.floor_le
      have h2: ⌊x / 3⌋ ≤ x / 3 := by apply Int.floor_le
      nlinarith [h1,h2,h]
    have hx3: 2.7 < x ∨ x < -3.5 := by
      by_contra! hx3
      rcases hx3 with ⟨hx3, hx4⟩
      nlinarith
    replace h: x ^ 2 = 10 - ⌊x / 2⌋ - ⌊x / 3⌋ := by
      nlinarith
    set a:= 10 - ⌊x / 2⌋ - ⌊x / 3⌋ with ha
    replace ha: ↑a = x ^ 2 := by   -- we will use the fact that a ∈ ℤ
      rw [h]
      norm_cast
    replace ha: x ^ 2 = ↑a := by simp [ha]
    clear ineq ineq2
    rcases hx3 with hx3 | hx3

    -- we first consider the case when x > 2.7
    . clear hx2
      -- we obtain bound for a
      have ha1: (7: ℝ) < a := by
        rw [← ha]
        nlinarith
      norm_cast at ha1
      replace ha1: 8 ≤ a := by omega
      have ha2: a < (10: ℝ) := by
        rw [← ha]
        nlinarith
      norm_cast at ha2
      replace ha2: a ≤ 9 := by omega
      have a_val: a = 8 ∨ a = 9 := by omega
      rcases a_val with a_val | a_val
      -- a = 8
      . simp [a_val] at *
        clear ha1 ha2 a_val
        have x_val: x = √8 := by
          symm
          rw [Real.sqrt_eq_iff_mul_self_eq_of_pos]
          linarith
          linarith
        simp [ha] at h
        rw [x_val] at h  -- now we directly compute h
        have eq1: ⌊√8 / 2⌋ = 1 := by
          rw [Int.floor_eq_iff]
          have h1: √8 < 3 := by
            rw [Real.sqrt_lt']
            norm_num
            norm_num
          have h2: 2 < √8 := by
            apply Real.lt_sqrt_of_sq_lt
            norm_num
          constructor
          . simp
            nlinarith [h1,h2]
          . simp
            nlinarith [h1,h2]
        have eq2: ⌊√8 / 3⌋ = 0 := by
          rw [Int.floor_eq_iff]
          have h1: √8 < 3 := by
            rw [Real.sqrt_lt']
            norm_num
            norm_num
          have h2: 2 < √8 := by
            apply Real.lt_sqrt_of_sq_lt
            norm_num
          constructor
          . simp
            nlinarith [h1,h2]
          . simp
            nlinarith [h1,h2]
        simp [eq1,eq2] at h
        absurd h
        norm_num
      -- a = 9
      . simp [a_val] at *
        clear ha1 ha2 a_val
        have x_val: x = 3 := by
          nlinarith
        simp [ha] at h
        rw [x_val] at h  -- now we directly compute h
        have eq1: ⌊(3: ℝ) / 2⌋ = 1 := by
          rw [Int.floor_eq_iff]
          norm_num
        have eq2: ⌊(3: ℝ) / 3⌋ = 1 := by
          rw [Int.floor_eq_iff]
          norm_num
        simp [eq1,eq2] at h
        absurd h
        norm_num
    -- Now we consider the case when x < -3.5
    . clear hx1
      -- we obtain bound for a
      have ha1: (12: ℝ) < a := by
        rw [← ha]
        nlinarith
      have ha2: a < (16: ℝ) := by
        rw [← ha]
        nlinarith
      replace ha1: 13 ≤ a := by norm_cast at ha1
      replace ha2: a ≤ 15 := by norm_cast at ha2; omega
      have a_val: a = 13 ∨ a = 14 ∨ a = 15 := by omega -- now we can check them all
      rcases a_val with a_val | a_val | a_val
      -- a = 13
      . simp [a_val] at *
        clear ha1 ha2 a_val
        have x_val: x = -√13 := by
          symm
          set y:= -x with hy
          have hy2: 0 < y := by nlinarith
          replace hy: x = -y := by linarith
          simp [hy]
          simp [hy] at ha
          rw [Real.sqrt_eq_iff_mul_self_eq_of_pos]
          linarith
          linarith
        simp [ha] at h
        rw [x_val] at h  -- now we directly compute h
        have eq1: ⌊-√13 / 2⌋ = -2 := by
          rw [Int.floor_eq_iff]
          have h1: √13 < 4 := by
            rw [Real.sqrt_lt']
            norm_num
            norm_num
          have h2: 3 < √13 := by
            apply Real.lt_sqrt_of_sq_lt
            norm_num
          constructor
          . simp
            nlinarith [h1,h2]
          . simp
            nlinarith [h1,h2]
        have eq2: ⌊-√13 / 3⌋ = -2 := by
          rw [Int.floor_eq_iff]
          have h1: √13 < 4 := by
            rw [Real.sqrt_lt']
            norm_num
            norm_num
          have h2: 3 < √13 := by
            apply Real.lt_sqrt_of_sq_lt
            norm_num
          constructor
          . simp
            nlinarith [h1,h2]
          . simp
            nlinarith [h1,h2]
        simp [eq1,eq2] at h
        absurd h
        norm_num
      -- a = 14
      . simp [a_val] at *
        clear ha1 ha2 a_val
        have x_val: x = -√14 := by
          symm
          set y:= -x with hy
          have hy2: 0 < y := by nlinarith
          replace hy: x = -y := by linarith
          simp [hy]
          simp [hy] at ha
          rw [Real.sqrt_eq_iff_mul_self_eq_of_pos]
          linarith
          linarith
        exact x_val
      -- a = 15
      . simp [a_val] at *
        clear ha1 ha2 a_val
        have x_val: x = -√15 := by
          symm
          set y:= -x with hy
          have hy2: 0 < y := by nlinarith
          replace hy: x = -y := by linarith
          simp [hy]
          simp [hy] at ha
          rw [Real.sqrt_eq_iff_mul_self_eq_of_pos]
          linarith
          linarith
        simp [ha] at h
        rw [x_val] at h  -- now we directly compute h
        have eq1: ⌊-√15 / 2⌋ = -2 := by
          rw [Int.floor_eq_iff]
          have h1: √15 < 4 := by
            rw [Real.sqrt_lt']
            norm_num
            norm_num
          have h2: 3 < √15 := by
            apply Real.lt_sqrt_of_sq_lt
            norm_num
          constructor
          . simp
            nlinarith [h1,h2]
          . simp
            nlinarith [h1,h2]
        have eq2: ⌊-√15 / 3⌋ = -2 := by
          rw [Int.floor_eq_iff]
          have h1: √15 < 4 := by
            rw [Real.sqrt_lt']
            norm_num
            norm_num
          have h2: 3 < √15 := by
            apply Real.lt_sqrt_of_sq_lt
            norm_num
          constructor
          . simp
            nlinarith [h1,h2]
          . simp
            nlinarith [h1,h2]
        simp [eq1,eq2] at h
        absurd h
        norm_num

  -- Next, we show that -√14 is in the set.
  . intro h
    simp at h
    simp [h]
    have eq1: ⌊-√14 / 2⌋ = -2 := by
      rw [Int.floor_eq_iff]
      have h1: √14 < 4 := by
        rw [Real.sqrt_lt']
        norm_num
        norm_num
      have h2: 3 < √14 := by
        apply Real.lt_sqrt_of_sq_lt
        norm_num
      constructor
      . simp
        nlinarith [h1,h2]
      . simp
        nlinarith [h1,h2]
    have eq2: ⌊-√14 / 3⌋ = -2 := by
      rw [Int.floor_eq_iff]
      have h1: √14 < 4 := by
        rw [Real.sqrt_lt']
        norm_num
        norm_num
      have h2: 3 < √14 := by
        apply Real.lt_sqrt_of_sq_lt
        norm_num
      constructor
      . simp
        nlinarith [h1,h2]
      . simp
        nlinarith [h1,h2]
    simp [eq1,eq2]
    norm_num