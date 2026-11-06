import Mathlib

def IsInt (x : ℝ) : Prop := ∃ m : ℤ, x = ↑m

lemma isInt_of_real_cast (z : ℤ) : IsInt (z : ℝ) := ⟨z, rfl⟩

lemma isInt_add {x y : ℝ} (hx : IsInt x) (hy : IsInt y) : IsInt (x + y) := by
  obtain ⟨zx, hzx⟩ := hx; obtain ⟨zy, hzy⟩ := hy
  use zx + zy; rw [hzx, hzy, Int.cast_add]

lemma isInt_sub {x y : ℝ} (hx : IsInt x) (hy : IsInt y) : IsInt (x - y) := by
  obtain ⟨zx, hzx⟩ := hx; obtain ⟨zy, hzy⟩ := hy
  use zx - zy; rw [hzx, hzy, Int.cast_sub]

lemma isInt_mul {x y : ℝ} (hx : IsInt x) (hy : IsInt y) : IsInt (x * y) := by
  obtain ⟨zx, hzx⟩ := hx; obtain ⟨zy, hzy⟩ := hy
  use zx * zy; rw [hzx, hzy, Int.cast_mul]

lemma newton_sum_identity (a b : ℝ) (k : ℕ) :
    (a^(k+2) + b^(k+2)) = (a+b) * (a^(k+1) + b^(k+1)) - (a*b) * (a^k + b^k) := by
  ring

theorem part1 (a b : ℝ)
    (hS1_ex : IsInt (a + b))
    (hS2_ex : IsInt (a^2 + b^2))
    (hS3_ex : IsInt (a^3 + b^3))
    (hS4_ex : IsInt (a^4 + b^4)) :
    ∀ n : ℕ, n > 0 → IsInt (a^n + b^n) := by
  let S n := a^n + b^n

  let s_val := a + b
  let p_val := a * b

  have h_two_p_val_is_int : IsInt (2 * p_val) := by
    obtain ⟨s1_int, hS1_eq⟩ := hS1_ex
    obtain ⟨s2_int, hS2_eq⟩ := hS2_ex
    use s1_int^2 - s2_int
    calc 2 * p_val
        = (a+b)^2 - (a^2+b^2) := by ring
      _ = (↑s1_int)^2 - (↑s2_int) := by rw [hS1_eq, hS2_eq]
      _ = ↑(s1_int^2 - s2_int) := by simp [Int.cast_sub, Int.cast_pow]
  obtain ⟨two_p_int, h_two_p_eq⟩ := h_two_p_val_is_int

  have h_two_p_sq_val_is_int : IsInt (2 * p_val^2) := by
    obtain ⟨s2_int, hS2_eq⟩ := hS2_ex
    obtain ⟨s4_int, hS4_eq⟩ := hS4_ex
    use s2_int^2 - s4_int
    calc 2 * p_val^2
        = (a^2+b^2)^2 - (a^4+b^4) := by simp only [p_val]; ring
      _ = (↑s2_int)^2 - (↑s4_int) := by rw [hS2_eq, hS4_eq]
      _ = ↑(s2_int^2 - s4_int) := by simp [Int.cast_sub, Int.cast_pow]
  obtain ⟨two_p_sq_int, h_two_p_sq_eq⟩ := h_two_p_sq_val_is_int

  have hp_val_is_int : IsInt p_val := by
    have h_int_eq : (↑two_p_int)^2 = ↑(2 * two_p_sq_int) := by
      have hp_val : p_val = (two_p_int : ℝ) / 2 := by 
        have h1 : (2 : ℝ) * p_val = (two_p_int : ℝ) := by
          exact_mod_cast h_two_p_eq
        have h2 : p_val = (two_p_int : ℝ) / 2 := by 
          linarith
        exact h2

      have h3 : 2 * p_val ^ 2 = (two_p_sq_int : ℝ) := by 
        exact_mod_cast h_two_p_sq_eq
      
      rw [hp_val] at h3
      
      have h4 : (two_p_int : ℝ) ^ 2 = 2 * (two_p_sq_int : ℝ) := by
        nlinarith
      
      exact_mod_cast h4
    have h_two_p_int_sq_even : Even (two_p_int^2) := by
      use two_p_sq_int
      simp_rw [h_int_eq]
      omega
    have h_two_p_int_even : Even two_p_int := (Int.even_pow' (by norm_num : 2 ≠ 0)).mp h_two_p_int_sq_even
    have h_exists_k_prop : ∃ k : ℤ, two_p_int = 2 * k := (even_iff_exists_two_mul).mp h_two_p_int_even
    obtain ⟨k, hk_even_def⟩ : ∃ k' : ℤ, two_p_int = 2 * k' := h_exists_k_prop
    rw [hk_even_def, Int.cast_mul, Int.cast_two] at h_two_p_eq
    have h_target_eq : p_val = ↑k := by
      apply (mul_right_inj' _).mp h_two_p_eq
      norm_num
    use k

  obtain ⟨p_int, hp_eq⟩ := hp_val_is_int
  obtain ⟨s_int, hs_eq⟩ := hS1_ex
  
  intro n_orig hn_pos_orig
  obtain ⟨k, hk⟩ : ∃ k, n_orig = k + 1 := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hn_pos_orig)
  rw [hk]
  subst hk

  induction k using Nat.twoStepInduction with
  | zero =>
    simp [hs_eq]
    use s_int
  | one =>
    exact hS2_ex
  | more k_n ih_k ih_kp1 =>
    rw [newton_sum_identity a b (k_n+1)] 
    apply isInt_sub
    · apply isInt_mul
      · simp [hs_eq]
        use s_int
      · apply ih_kp1
        linarith
    · apply isInt_mul
      · unfold p_val at hp_eq
        rw [hp_eq]
        use p_int
      · apply ih_k
        linarith

-- For Part 2
theorem part2_statement_is_false :
    ¬ (∀ (a b : ℝ), IsInt (a+b) → IsInt (a^2+b^2) → IsInt (a^3+b^3) →
                      (∀ n : ℕ, n > 0 → IsInt (a^n+b^n))) := by
  push_neg
  let aval := 1 + 1 / Real.sqrt 2
  let bval := 1 - 1 / Real.sqrt 2
  use aval, bval

  let S n := aval^n + bval^n

  have h_sqrt2_ne_zero : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have h_aval_bval_def : aval = 1 + 1/Real.sqrt 2 ∧ bval = 1 - 1/Real.sqrt 2 := by constructor; rfl; rfl

  have hS1 : S 1 = 2 := by
    simp only [S, pow_one]
    calc aval + bval = (1 + 1/Real.sqrt 2) + (1 - 1/Real.sqrt 2) := by rfl
                   _ = 2 := by ring
  have hS2 : S 2 = 3 := by
    simp only [S]
    calc aval^2 + bval^2 = (1 + 1/Real.sqrt 2)^2 + (1 - 1/Real.sqrt 2)^2 := by rfl
                       _ = (1 + 2/Real.sqrt 2 + 1/2) + (1 - 2/Real.sqrt 2 + 1/2) := by ring_nf;norm_num
                       _ = (3/2 + 2/Real.sqrt 2) + (3/2 - 2/Real.sqrt 2) := by ring_nf
                       _ = 3 := by ring
  have hS3 : S 3 = 5 := by
    simp only [S]
    calc aval^3 + bval^3
        = (1 + 1/Real.sqrt 2)^3 + (1 - 1/Real.sqrt 2)^3 := by rfl
      _ = (1 + 3*(1/Real.sqrt 2) + 3*(1/Real.sqrt 2)^2 + (1/Real.sqrt 2)^3) +
          (1 - 3*(1/Real.sqrt 2) + 3*(1/Real.sqrt 2)^2 - (1/Real.sqrt 2)^3) := by ring
      _ = 2 + 6*(1/Real.sqrt 2)^2 := by ring
      _ = 2 + 6*(1/2) := by norm_num
      _ = 2 + 3 := by norm_num
      _ = 5 := by norm_num

  have hS4_val : S 4 = 17/2 := by
    simp only [S]
    have subt : 2 + 12 * (1 / √2) ^ 2 + 2 * (1 / √2) ^ 4 = 2 + 12 * (1 / 2) + 2 * (1 / 4) := by 
      have h1 : (1 / √2) ^ 2 = 1 / 2 := by
        have h2 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by linarith)
        field_simp
      have h3 : (1 / √2) ^ 4 = 1 / 4 := by
        calc
          (1 / √2) ^ 4 = ((1 / √2) ^ 2) ^ 2 := by ring
          _ = (1 / 2) ^ 2 := by rw [h1]
          _ = 1 / 4 := by norm_num
      rw [h1, h3]
    calc aval^4 + bval^4
        = (1 + 1/Real.sqrt 2)^4 + (1 - 1/Real.sqrt 2)^4 := by rfl
      _ = (1 + 4*(1/Real.sqrt 2) + 6*(1/Real.sqrt 2)^2 + 4*(1/Real.sqrt 2)^3 + (1/Real.sqrt 2)^4) +
          (1 - 4*(1/Real.sqrt 2) + 6*(1/Real.sqrt 2)^2 - 4*(1/Real.sqrt 2)^3 + (1/Real.sqrt 2)^4) := by ring
      _ = 2 + 12*(1/Real.sqrt 2)^2 + 2*(1/Real.sqrt 2)^4 := by ring
      _ = 2 + 12*(1/2) + 2*(1/4) := by rw [subt]
      _ = 2 + 6 + 1/2 := by norm_num
      _ = 8 + 1/2 := by norm_num
      _ = 17/2 := by norm_num

  have hS1_is_int : IsInt (S 1) := by rw [hS1]; use 2; simp
  have hS2_is_int : IsInt (S 2) := by rw [hS2]; use 3; simp
  have hS3_is_int : IsInt (S 3) := by rw [hS3]; use 5; simp

  have hS4_not_int : ¬ IsInt (S 4) := by
    rw [hS4_val]
    intro h_is_int
    obtain ⟨k, hk_eq⟩ := h_is_int
    have : (17:ℝ) = ↑(2*k) := by
      apply_fun (· * (2:ℝ)) at hk_eq
      field_simp [h_sqrt2_ne_zero] at hk_eq
      rw [mul_comm] at hk_eq
      simpa using hk_eq
    have h_17_even : Even (17:ℤ) := by
      use k
      have h1 : 17 = 2 * k := by
        norm_num at this
        exact_mod_cast this
      omega
    have h_17_odd : Odd (17:ℤ) := by use 8; norm_num
    contradiction

  unfold aval bval
  simp
  
  constructor
  · use 2
    simp
    linarith
  · constructor
    · use 3
      simp
      have h1 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)
      have h2 : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
        field_simp
      have h3 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      rw [h2]
      nlinarith [h3,Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    · constructor
      · use 5
        simp
        have h1 : (Real.sqrt 2)⁻¹ = (Real.sqrt 2) / 2 := by 
          field_simp
        rw [h1]
        have h2 : (1 + (Real.sqrt 2 / 2)) ^ 3 + (1 - (Real.sqrt 2 / 2)) ^ 3 = 5 := by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (2 : ℝ) > 0), 
            Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (2 : ℝ) ≥ 0)]
        linarith only [h2]
      · use 4
        simp
        intro h
        rcases h with ⟨n, hn⟩
        have h3 : (1 + 1 / √2) ^ 4 + (1 - 1 / √2) ^ 4 = 17 / 2 := by
          have h2 : (√2) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
          have h3 : (1 + 1 / √2) = (√2 + 1) / √2 := by field_simp [h2]
          have h4 : (1 - 1 / √2) = (√2 - 1) / √2 := by field_simp [h2]
          rw [h3, h4]
          have h5 : (√2 + 1) ^ 4 + (√2 - 1) ^ 4 = 34 := by
            nlinarith [h2, Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
          have h6 : (√2) ^ 4 = 4 := by
            calc
              (√2) ^ 4 = ((√2) ^ 2) ^ 2 := by ring
              _ = 2 ^ 2 := by rw [h2]
              _ = 4 := by norm_num
          field_simp [h6]
          linarith [h5]
        have h4 : (n : ℝ) = 17 / 2 := by
          have hh : (1 + (√2)⁻¹) ^ 4 + (1 - (√2)⁻¹) ^ 4 = (1 + 1 / √2) ^ 4 + (1 - 1 / √2) ^ 4 := by ring_nf
          rw [← hn,hh,h3]
        have h5 : (n : ℝ) = (n : ℤ) := by simp
        rw [h5] at h4
        have h6 : 2 * (n : ℤ) = 17 := by
          have h7 : (n : ℝ) = 17 / 2 := h4
          have h8 : (2 : ℝ) * (n : ℝ) = 17 := by
            linarith [h7]
          have h9 : (2 : ℤ) * (n : ℤ) = 17 := by
            exact_mod_cast h8
          exact_mod_cast h9
        have h7 : (n : ℤ) = 8 := by omega
        omega

theorem algebra_604459_1 (a b : ℝ)
    (ha : ∃ m : ℤ, a + b = m)
    (hb : ∃ m : ℤ, a^2 + b^2 = m)
    (hc : ∃ m : ℤ, a^3 + b^3 = m)
    (hd : ∃ m : ℤ, a^4 + b^4 = m) :
    ∀ n : ℕ, n > 0 → ∃ m : ℤ, a^n + b^n = m :=
  part1 a b ha hb hc hd

theorem algebra_604459_2 :
  ¬ (∀ (a b : ℝ)
    (ha : ∃ m : ℤ, a + b = m)
    (hb : ∃ m : ℤ, a^2 + b^2 = m)
    (hc : ∃ m : ℤ, a^3 + b^3 = m),
    ∀ n : ℕ, n > 0 → ∃ m : ℤ, a^n + b^n = m) := by
  intro h_P_true
  apply part2_statement_is_false
  exact h_P_true