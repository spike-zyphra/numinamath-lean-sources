import Mathlib

open Real

-- Prove that if a, b, c > 1 or 0 < a, b, c < 1, then log_b(a^2)/(a + b) + log_c(b^2)/(b + c) + log_a(c^2)/(c + a) ≥ 9 / (a + b + c).
theorem inequalities_215140 (a b c : ℝ)(h : (a > 1 ∧ b > 1 ∧ c > 1) ∨ ((0 < a ∧ a < 1) ∧ (0 < b ∧ b < 1) ∧ (0 < c ∧ c < 1))) : (logb b (a^2)) / (a + b) + (logb c (b^2)) / (b + c) + (logb a (c^2)) / (c + a) ≥ 9 / (a + b + c) := by
  -- Step 1: Prove positivity of each term in the sum
  have hlogpos : logb b a / (a + b) > 0 ∧ logb c b / (b + c) > 0 ∧ logb a c / (c + a) > 0 := by
    rcases h with h1 | h2
    · -- Case 1: a, b, c > 1
      constructor
      · apply div_pos
        -- logb b a > 0 since a > 1 and b > 1
        · apply logb_pos h1.2.1 h1.1
        linarith
      · constructor
        · apply div_pos
          -- logb c b > 0 since b > 1 and c > 1
          · apply logb_pos h1.2.2 h1.2.1
          linarith
        · apply div_pos
          -- logb a c > 0 since c > 1 and a > 1
          · apply logb_pos h1.1 h1.2.2
          linarith
    · -- Case 2: 0 < a, b, c < 1
      constructor
      · apply div_pos
        -- logb b a > 0 when 0 < a, b < 1
        · apply (logb_pos_iff_of_base_lt_one h2.2.1.1 h2.2.1.2 (by linarith)).mpr (by linarith)
        linarith
      · constructor
        · apply div_pos
          -- logb c b > 0 when 0 < b, c < 1
          · apply (logb_pos_iff_of_base_lt_one h2.2.2.1 h2.2.2.2 (by linarith)).mpr (by linarith)
          linarith
        · apply div_pos
          -- logb a c > 0 when 0 < c, a < 1
          · apply (logb_pos_iff_of_base_lt_one h2.1.1 h2.1.2 (by linarith)).mpr (by linarith)
          linarith

  -- Step 2: Apply the AM-GM inequality to bound the sum
  have add_ge_mul : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → a + b + c ≥ 3 * (a * b * c)^((1:ℝ)/3) := by
    intro a b c habc
    let x := a ^ ((1:ℝ)/3)
    let y := b ^ ((1:ℝ)/3)
    let z := c ^ ((1:ℝ)/3)
    -- Rewrite a, b, c in terms of their cubic roots
    have : ∀ (a:ℝ), a > 0 → a = (a^((1:ℝ)/3))^3 := by
      intro a ha
      have := @Real.rpow_inv_natCast_pow a 3 (by linarith) (by linarith)
      simp at this
      simp
      rw [this]
    rw [this a (by linarith), this b (by linarith), this c (by linarith)]
    have hx : x = a ^ ((1:ℝ)/3) := rfl
    have hy : y = b ^ ((1:ℝ)/3) := rfl
    have hz : z = c ^ ((1:ℝ)/3) := rfl
    have hxpos : x > 0 := by refine rpow_pos_of_pos ?hx (1 / 3); linarith
    have hypos : y > 0 := by refine rpow_pos_of_pos ?hy (1 / 3); linarith
    have hzpos : z > 0 := by refine rpow_pos_of_pos ?hz (1 / 3); linarith
    rw [← hx, ← hy, ← hz]
    -- Use the AM-GM inequality in terms of x, y, z
    have heq : x ^ 3 * y ^ 3 * z ^ 3 = (x * y * z) ^ 3 := by
      rw [mul_pow, mul_pow]
    rw [heq]
    have : ((x * y * z) ^ 3) ^ ((1:ℝ)/3) = x * y * z := by
      have := @Real.rpow_mul (x*y*z) ?h 3 ((1:ℝ)/3)
      simp at this
      simp
      nth_rw 2 [this]
      norm_cast
      apply mul_nonneg
      · apply mul_nonneg
        · linarith
        · linarith
      · linarith
    rw [this]
    -- Prove the inequality using sum of squares
    have : 2 * (x ^ 3 + y ^ 3 + z ^ 3 - 3 * (x * y * z)) ≥ 0 := by
      calc
        _ = (x + y + z)*((x-y)^2+(y-z)^2+(z-x)^2) := by ring
        _ ≥ _ := by
          apply mul_nonneg
          · linarith
          · nlinarith
    linarith

  -- Step 3: Prove positivity of a, b, c
  have hpos : a > 0 ∧ b > 0 ∧ c > 0 := by
    rcases h with h1 | h2
    · constructor
      · linarith
      · constructor
        · linarith
        · linarith
    · constructor
      · linarith
      · constructor
        · linarith
        · linarith

  -- Step 4: Prove that a, b, c are not equal to 1
  have hnzero : a ≠ 1 ∧ b ≠ 1 ∧ c ≠ 1:= by
    constructor
    · intro ha
      rw [ha] at h
      rcases h with h1 | h2
      · linarith
      · linarith
    · constructor
      · intro hb
        rw [hb] at h
        rcases h with h1 | h2
        · linarith
        · linarith
      · intro hc
        rw [hc] at h
        rcases h with h1 | h2
        · linarith
        · linarith

  -- Step 5: Simplify and apply AM-GM inequality to the main expression
  calc
    _ = 2 * (logb b a) / (a + b) + 2 * (logb c b) / (b + c) + 2 * (logb a c) / (c + a) := by
      rw [logb_pow, logb_pow, logb_pow]
      simp
    _ = 2 * ((logb b a) / (a + b) + (logb c b) / (b + c) + (logb a c) / (c + a)) := by ring
    _ ≥ 2 * (3 * (((logb b a) / (a + b) * ((logb c b) / (b + c)) * ((logb a c) / (c + a)))^((1:ℝ)/3))) := by
      have := add_ge_mul ((logb b a) / (a + b)) ((logb c b) / (b + c)) ((logb a c) / (c + a)) hlogpos
      apply (mul_le_mul_iff_of_pos_left (by linarith)).mpr this
    _ = 2 * (3 * (((logb b a) * (logb c b) * (logb a c)) / ((a+b)*(b+c)*(c+a)))^((1:ℝ)/3)) := by
      rw [div_mul_div_comm, div_mul_div_comm]
    _ = 2 * (3 * (1 / ((a+b)*(b+c)*(c+a)))^((1:ℝ)/3)) := by
      nth_rw 4 [mul_comm]
      rw [@mul_logb c b a (by linarith) hnzero.2.1 (by linarith)]
      rw [@mul_logb c a c (by linarith) hnzero.1 (by linarith)]
      rw [Real.logb_self_eq_one_iff.mpr ⟨(by linarith), hnzero.2.2, (by linarith)⟩]
    _ = 6 / ((a+b)*(b+c)*(c+a))^((1:ℝ)/3) := by
      rw [div_rpow]
      · rw [← mul_assoc]
        have : (2 :ℝ)* 3 = 6 := by norm_num
        rw [this]
        have : (1:ℝ) ^ ((1:ℝ)/3) = 1 := by norm_num
        rw [this]
        rw [← mul_div_assoc]
        simp
      · linarith
      · apply mul_nonneg
        · apply mul_nonneg
          · linarith
          · linarith
        · linarith
    _ ≥ 6 / (((a+b)+(b+c)+(c+a)) / 3) := by
      have hpos' : a + b > 0 ∧ b + c > 0 ∧ c + a > 0 := by
        constructor
        · linarith
        · constructor
          · linarith
          · linarith
      have := add_ge_mul (a+b) (b+c) (c+a) hpos'
      have : ((a+b)*(b+c)*(c+a))^((1:ℝ)/3) ≤ ((a+b)+(b+c)+(c+a)) / 3 := by
        linarith
      apply div_le_div_of_nonneg_left (by linarith)
      · apply rpow_pos_of_pos
        apply mul_pos
        · apply mul_pos
          · linarith
          · linarith
        · linarith
      · exact this
    _ = _ := by
      field_simp
      have : a + b + (b + c) + (c + a) = 2 * (a + b + c) := by ring
      rw [this]
      rw [div_mul_eq_div_div]
      ring
