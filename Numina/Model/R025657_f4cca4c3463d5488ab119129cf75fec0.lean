import Mathlib

theorem algebra_73656 (f : ℝ → ℝ) (hf : f = fun x => 2^(3*x+1) - 17 * 2^(2*x) + 2^(x+3)) :
    ∏ᶠ x ∈ {x | f x = 0}, x = -3 := by
  have h1 : {x : ℝ | f x = 0} = {-1, 3} := by
    ext x
    simp [hf]
    constructor
    · -- Assume f x = 0, prove x ∈ {-1, 3}
      intro h_eq
      have eq1 : (2 : ℝ) ^ (3 * x + 1) - 17 * (2 : ℝ) ^ (2 * x) + (2 : ℝ) ^ (x + 3) = 0 := by
        simpa using h_eq
      have eq2 : (2 : ℝ) ^ (3 * x + 1) = 2 * ((2 : ℝ) ^ x) ^ 3 := by
        have h4 : (2 : ℝ) ^ (3 * x + 1) = (2 : ℝ) ^ (3 * x) * (2 : ℝ) ^ (1 : ℝ) := by
          rw [← Real.rpow_add]
          ring_nf
          all_goals linarith
        have h5 : (2 : ℝ) ^ (3 * x) = ((2 : ℝ) ^ x) ^ 3 := by
          have h7 : (2 : ℝ) ^ (3 * x) = ((2 : ℝ) ^ x) ^ 3 := by
            calc
              (2 : ℝ) ^ (3 * x) = (2 : ℝ) ^ (3 * x) := by rfl
              _ = ((2 : ℝ) ^ x) ^ 3 := by 
                rw [← Real.rpow_natCast, ← Real.rpow_mul]
                ring_nf
                all_goals linarith
          exact h7
        have h6 : (2 : ℝ) ^ (1 : ℝ) = (2 : ℝ) := by
          norm_num
        rw [h4, h5, h6]
        all_goals ring
      have eq3 : (2 : ℝ) ^ (2 * x) = ((2 : ℝ) ^ x) ^ 2 := by 
        calc
          (2 : ℝ) ^ (2 * x) = ((2 : ℝ) ^ x) ^ 2 := by 
            rw [← Real.rpow_natCast, ← Real.rpow_mul]
            ring_nf
            all_goals linarith
          _ = ((2 : ℝ) ^ x) ^ 2 := by rfl
      have eq4 : (2 : ℝ) ^ (x + 3) = 8 * ((2 : ℝ) ^ x) := by
        have h7 : (2 : ℝ) ^ (x + 3) = (2 : ℝ) ^ x * (2 : ℝ) ^ (3 : ℝ) := by 
          rw [← Real.rpow_add]
          ring_nf
          all_goals linarith
        have h8 : (2 : ℝ) ^ (3 : ℝ) = (8 : ℝ) := by
          norm_num
        rw [h7, h8]
        all_goals ring
      rw [eq2, eq3, eq4] at eq1
      have eq5 : 2 * ((2 : ℝ) ^ x) ^ 3 - 17 * ((2 : ℝ) ^ x) ^ 2 + 8 * ((2 : ℝ) ^ x) = 0 := by
        linarith
      have h2powx_pos : (2 : ℝ) ^ x > 0 := by positivity
      have eq6 : ((2 : ℝ) ^ x) * (2 * ((2 : ℝ) ^ x) ^ 2 - 17 * ((2 : ℝ) ^ x) + 8) = 0 := by
        linarith [eq5]
      cases' (mul_eq_zero.mp eq6) with eq7 eq8
      · -- Case where (2 : ℝ) ^ x = 0
        nlinarith
      · -- Case where the quadratic expression is zero
        have eq9 : 2 * ((2 : ℝ) ^ x) ^ 2 - 17 * ((2 : ℝ) ^ x) + 8 = 0 := by linarith [eq8]
        have eq2powx : (2 : ℝ) ^ x = (8 : ℝ) ∨ (2 : ℝ) ^ x = (1 / 2 : ℝ) := by
          have h11 : (2 * ((2 : ℝ) ^ x) ^ 2 - 17 * ((2 : ℝ) ^ x) + 8) = 0 := eq9
          have h12 : ((2 : ℝ) ^ x - (8 : ℝ)) * ((2 : ℝ) ^ x - (1 / 2 : ℝ)) = 0 := by
            nlinarith
          cases' (mul_eq_zero.mp h12) with h13 h14
          · -- Case where ((2 : ℝ) ^ x) - 8 = 0
            left
            linarith
          · -- Case where ((2 : ℝ) ^ x) - (1 / 2) = 0
            right
            linarith
        cases eq2powx with
        | inl h2pow8 =>
          have hx1 : x = (3 : ℝ) := by
            have h2pow8' : (2 : ℝ) ^ x = (8 : ℝ) := h2pow8
            have h8 : (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) := by norm_num
            rw [h8] at h2pow8'
            have h9 : x = (3 : ℝ) := by
              apply_fun (Real.logb (2 : ℝ)) at h2pow8'
              have h10 : Real.logb (2 : ℝ) ((2 : ℝ) ^ x) = Real.logb (2 : ℝ) ((2 : ℝ) ^ (3 : ℝ)) := by
                linarith [h2pow8']
              rw [Real.logb_rpow, Real.logb_rpow] at h10
              all_goals linarith
            exact_mod_cast h9
          right
          linarith
        | inr h2pow1_2 =>
          have hx1 : x = (-1 : ℝ) := by
            have h2pow1_2' : (2 : ℝ) ^ x = (1 / 2 : ℝ) := h2pow1_2
            have h1_2 : (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) := by norm_num
            rw [h1_2] at h2pow1_2'
            have h9 : x = (-1 : ℝ) := by
              apply_fun (Real.logb (2 : ℝ)) at h2pow1_2'
              have h10 : Real.logb (2 : ℝ) ((2 : ℝ) ^ x) = Real.logb (2 : ℝ) ((2 : ℝ) ^ (-1 : ℝ)) := by
                linarith [h2pow1_2']
              rw [Real.logb_rpow, Real.logb_rpow] at h10
              all_goals linarith
            exact_mod_cast h9
          left
          linarith
    · -- Assume x ∈ {-1, 3}, prove f x = 0
      rintro (h_eq | h_eq)
      · -- Case where x = -1
        rw [h_eq]
        norm_num [hf]
      · -- Case where x = 3
        rw [h_eq]
        norm_num [hf]
  rw [h1]
  rw [finprod_mem_pair (by norm_num)]
  all_goals norm_num