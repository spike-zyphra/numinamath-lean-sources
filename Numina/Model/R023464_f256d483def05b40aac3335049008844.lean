import Mathlib

theorem algebra_94360 (f : ℝ → ℝ) (hf : f = fun x => 3^(2*x+2) - 3^(x+3) - 3^x + 3) :
    Set.ncard {x | f x = 0} = 2 := by
  have h1 : {x : ℝ | f x = 0} = {-2, 1} := by
    ext x
    simp [hf]
    constructor
    · -- Assume $f(x) = 0$, prove $x \in \{-2, 1\}$.
      intro h
      have h2 : (3 : ℝ) ^ (2 * x + 2) - (3 : ℝ) ^ (x + 3) - (3 : ℝ) ^ x + 3 = 0 := by
        simpa using h
      have h3 : (3 : ℝ) ^ (2 * x + 2) = 9 * ((3 : ℝ) ^ x) ^ 2 := by
        calc
          (3 : ℝ) ^ (2 * x + 2) = (3 : ℝ) ^ (2 * x) * (3 : ℝ) ^ (2 : ℝ) := by rw [← Real.rpow_add]; ring_nf; all_goals linarith
          _ = (3 : ℝ) ^ (2 * x) * 9 := by norm_num
          _ = 9 * ((3 : ℝ) ^ x) ^ 2 := by
            have h4 : (3 : ℝ) ^ (2 * x) = ((3 : ℝ) ^ x) ^ 2 := by
              calc
                (3 : ℝ) ^ (2 * x) = (3 : ℝ) ^ (x * 2) := by ring_nf
                _ = ((3 : ℝ) ^ x) ^ 2 := by rw [← Real.rpow_natCast, ← Real.rpow_mul]; ring_nf; all_goals linarith
            rw [h4]
            <;> ring_nf
      have h4 : (3 : ℝ) ^ (x + 3) = 27 * (3 : ℝ) ^ x := by
        calc
          (3 : ℝ) ^ (x + 3) = (3 : ℝ) ^ x * (3 : ℝ) ^ (3 : ℝ) := by rw [← Real.rpow_add]; ring_nf; all_goals linarith
          _ = (3 : ℝ) ^ x * 27 := by norm_num
          _ = 27 * (3 : ℝ) ^ x := by ring_nf
      rw [h3, h4] at h2
      have h5 : 9 * ((3 : ℝ) ^ x) ^ 2 - 28 * (3 : ℝ) ^ x + 3 = 0 := by
        linarith
      have h6 : ((3 : ℝ) ^ x - 3) * ((3 : ℝ) ^ x - 1 / 9) = 0 := by
        nlinarith
        all_goals nlinarith
      cases' (mul_eq_zero.mp h6) with h7 h8
      · -- Case $3^x - 3 = 0$
        have h8 : (3 : ℝ) ^ x = 3 := by
          linarith
        have h9 : x = 1 := by
          have h10 : Real.logb (3 : ℝ) ((3 : ℝ) ^ x) = Real.logb (3 : ℝ) (3 : ℝ) := by
            rw [h8]
          have h11 : Real.logb (3 : ℝ) ((3 : ℝ) ^ x) = x := by
            rw [Real.logb_rpow]
            all_goals norm_num
          have h12 : Real.logb (3 : ℝ) (3 : ℝ) = 1 := by
            norm_num [Real.logb_eq_iff_rpow_eq]
          rw [h11, h12] at h10
          linarith
        right
        linarith
      · -- Case $3^x - 1/9 = 0$
        have h10 : (3 : ℝ) ^ x = 1 / 9 := by
          linarith
        have h11 : x = -2 := by
          have h14 : Real.logb (3 : ℝ) ((3 : ℝ) ^ x) = Real.logb (3 : ℝ) (1 / 9) := by
            rw [h10]
          have h13 : Real.logb (3 : ℝ) ((3 : ℝ) ^ x) = x := by
            rw [Real.logb_rpow]
            all_goals norm_num
          have h14' : Real.logb (3 : ℝ) (1 / 9) = -2 := by
            have h15 : Real.logb (3 : ℝ) (1 / 9) = Real.logb (3 : ℝ) (1) - Real.logb (3 : ℝ) (9) := by
              field_simp [Real.logb_div]
            have h16 : Real.logb (3 : ℝ) (1) = 0 := by
              norm_num [Real.logb_one]
            have h17 : Real.logb (3 : ℝ) (9) = 2 := by
              have : (9 : ℝ) = (3 : ℝ) ^ (2 : ℝ) := by norm_num
              rw [this]
              have h21 : Real.logb (3 : ℝ) ((3 : ℝ) ^ (2 : ℝ)) = (2 : ℝ) := by
                rw [Real.logb_rpow]
                all_goals norm_num
              linarith
            rw [h15, h16, h17]
            all_goals norm_num
          rw [h13, h14'] at h14
          linarith
        left
        linarith
    · -- Assume $x \in \{-2, 1\}$, prove $f(x) = 0$.
      intro hx
      rcases hx with (rfl | rfl)
      · -- x = -2
        norm_num [Real.rpow_natCast, Real.rpow_intCast, Real.rpow_add]
      · -- x = 1
        norm_num [Real.rpow_natCast, Real.rpow_intCast, Real.rpow_add]
  rw [h1]
  norm_num [Set.ncard_pair]
  all_goals norm_num