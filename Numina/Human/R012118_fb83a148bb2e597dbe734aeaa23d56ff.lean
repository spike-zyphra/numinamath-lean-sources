import Mathlib

open Real

theorem algebra_609402 :
  IsGreatest {θ : ℝ | θ < π ∧
    (∏ k ∈ Finset.range 11, cos (2^k * θ)) ≠ 0 ∧
    (∏ k ∈ Finset.range 11, (1 + 1 / cos (2^k * θ))) = 1}
    ((2046 * π) / 2047) := by
  -- Define our candidate solution
  let θ₀ : ℝ := (2046 * π) / 2047

  let S := {θ : ℝ | θ < π ∧
    (∏ k ∈ Finset.range 11, cos (2^k * θ)) ≠ 0 ∧
    (∏ k ∈ Finset.range 11, (1 + 1 / cos (2^k * θ))) = 1}

  -- Step 1: Prove the induction identity
  -- Base case: n = 0
  have base_case : ∀ θ : ℝ,  cos θ ≠ 0 → (1 + 1 / cos θ)* sin (θ / 2) = tan θ * cos (θ / 2) := by
    intro θ h_nonzero
    rw [tan_eq_sin_div_cos]
    field_simp

    have : sin θ = sin (2 * (θ / 2)) := by ring_nf
    rw [this, sin_two_mul]

    have : cos θ = cos (2 * (θ / 2)) := by ring_nf
    rw [this, cos_two_mul]
    field_simp
    ring_nf

  -- Inductive step
  have induction_step : ∀ (θ : ℝ) (n : ℕ), (∏ k ∈ Finset.range (n+1), cos (2 ^ k * θ) ≠ 0 → (∏ k ∈ Finset.range (n+1), (1 + 1 / cos (2^k * θ))) * sin (θ / 2) = tan (2^n * θ) * cos (θ / 2)) →
    (∏ k ∈ Finset.range (n+2), cos (2 ^ k * θ) ≠ 0 → (∏ k ∈ Finset.range (n+2), (1 + 1 / cos (2^k * θ))) * sin (θ / 2) = tan (2^(n+1) * θ) * cos (θ / 2)) := by
    intro θ n h_ind h_θ

    have : ∏ k ∈ Finset.range (n + 1), cos (2 ^ k * θ) ≠ 0 := by
      rw [Finset.prod_range_succ, mul_ne_zero_iff] at h_θ
      exact h_θ.1

    rw [Finset.prod_range_succ]
    rw [(by ring : (∏ x ∈ Finset.range (n + 1), (1 + 1 / cos (2 ^ x * θ))) * (1 + 1 / cos (2 ^ (n + 1) * θ)) * sin (θ / 2) = (∏ x ∈ Finset.range (n + 1), (1 + 1 / cos (2 ^ x * θ))) * sin (θ / 2) * (1 + 1 / cos (2 ^ (n + 1) * θ)))]
    rw [h_ind this]

    let x := 2^(n+1) * θ
    have h1: 2^(n+1) * θ = x := by rfl
    have h2: 2^n * θ = x / 2 := by ring

    have h_cos_1: cos x ≠ 0 := by
      rw [Finset.prod_range_succ, mul_ne_zero_iff] at h_θ
      exact h_θ.2

    have h_cos_2: cos (x/2) ≠ 0 := by
      rw [Finset.prod_range_succ, mul_ne_zero_iff] at this
      rw [(by ring: 2 ^ (n + 1) * θ / 2 = 2 ^ n * θ)]
      exact this.2
    rw [h1, h2]

    have : (1 + 1 / cos x) * tan (x / 2) = tan x := by
      rw [tan_eq_sin_div_cos, mul_div_assoc', base_case x h_cos_1]
      field_simp

    rw [mul_comm, ←mul_assoc, this]

  -- Conclude the product formula
  have product_formula : ∀ θ : ℝ , (∏ k ∈ Finset.range 11, cos (2^k * θ)) ≠ 0 →
    (∏ k ∈ Finset.range 11, (1 + 1 / cos (2^k * θ))) * sin (θ / 2) = tan (2^10 * θ) * cos (θ / 2) := by
    intro θ h_θ
    have h_ind : ∀ n : ℕ, (∏ k ∈ Finset.range (n + 1), cos (2^k * θ)) ≠ 0 →
    (∏ k ∈ Finset.range (n + 1), (1 + 1 / cos (2^k * θ))) * sin (θ / 2) = tan (2^n * θ) * cos (θ / 2) := by
      intro n; induction n
      case zero =>
        field_simp
        exact base_case θ
      case succ n' ih =>
        exact induction_step θ n' ih
    exact h_ind 10 h_θ

  -- Step 2: Prove θ₀ is an upper bound
  have h_upper : ∀ θ ∈ S, θ ≤ θ₀ := by
    intro θ h_θ

    have sin_equation : sin (2 ^ 10 * θ - θ / 2) = 0 := by
      have formula := product_formula θ h_θ.2.1
      rw [h_θ.2.2] at formula
      rw [tan_eq_sin_div_cos] at formula
      field_simp at formula

      have : sin (2 ^ 10 * θ - θ / 2) = 0 := by
        rw [sin_sub, sub_eq_zero]
        rw [formula]
        have : cos (2 ^ 10 * θ) ≠ 0 := by
          have h:= h_θ.2.1
          rw [Finset.prod_range_succ, mul_ne_zero_iff] at h
          exact h.2
        field_simp

      exact this

    -- Solve for θ = 2mπ/2047 for some integer m
    have theta_form : ∃ (m : ℤ), θ = (2 * m * π) / 2047 := by
      rw [sin_eq_zero_iff] at sin_equation
      obtain ⟨k, hk⟩ := sin_equation
      use k
      field_simp at hk
      ring_nf at hk
      have : k * π * 2 = 2 * k * π := by ring
      rw [this] at hk
      rw [hk]
      field_simp

    obtain ⟨m, hm⟩ := theta_form
    have m_max : m ≤ 1023 := by
      have h1 : θ < π := h_θ.1
      rw [hm] at h1
      rw [(by ring : 2 * ↑m * π / 2047 = (π / 2047) * (2 *↑m))] at h1
      nth_rw 2 [(by ring : π = (π / 2047) * 2047)] at h1
      have h2 := lt_of_mul_lt_mul_of_nonneg_left h1 (by positivity : 0 ≤ (π / 2047))
      by_contra h_contra
      simp at h_contra
      have : 2 * m > 2 * 1023 := mul_lt_mul_of_pos_left h_contra (by linarith : (0 : ℤ) < 2)
      have := lt_of_lt_of_le h2 (by norm_cast : (2 * m : ℝ) ≥ 2047)
      linarith

    unfold θ₀
    rw [hm]
    have : (m : ℝ) ≤ 1023 := by exact_mod_cast m_max
    have h: (2 * π / 2047) * m  ≤ (2 * π / 2047) *  1023 := by
      apply mul_le_mul_of_nonneg_left this
      positivity

    have : (2 * ↑m * π) / 2047 = (2 * π / 2047) * m := by ring
    rw [this]
    have : 2046 * π / 2047 = (2 * π / 2047) * 1023 := by ring
    rw [this]
    exact h

  -- Step 3: Prove θ₀ is in our set
  have h_mem : θ₀ ∈ S := by
    -- Show that θ₀ < π
    have h_less_than_pi : θ₀ < π := by
      -- θ₀ = (2046 * π) / 2047 < π because 2046 < 2047
      have : π > 0 := pi_pos
      unfold θ₀
      linarith

    -- Show that ∏ cos(2^k * θ₀) ≠ 0
    have h_prod_cos_nonzero : (∏ k ∈ Finset.range 11, cos (2^k * θ₀)) ≠ 0 := by
      -- For each k, 2^k * θ₀ = 2^k * 2046 * π / 2047
      -- Since 2047 is odd and prime, 2^k * 2046 is not a multiple of 2047
      -- Therefore, cos(2^k * θ₀) ≠ 0 for all k
      unfold θ₀
      by_contra h_contra
      rw [Finset.prod_eq_zero_iff] at h_contra
      obtain ⟨k, hk⟩ := h_contra
      rw [cos_eq_zero_iff] at hk
      obtain ⟨m, hm⟩ := hk.2
      -- Simplify the original equation to get even = odd
      field_simp at hm
      rw [(by ring : 2 ^ k * (2046 * π) * 2 = (2 ^ (k + 1) * 2046) * π)] at hm
      rw [(by ring : (2 * ↑m + 1) * π * 2047 = ((2 * ↑m + 1) * 2047) * π)] at hm
      field_simp at hm
      cases' hm with hm_1 hm_2
      . -- 尝试遍历完所有的k : 从 0 到 10
        norm_cast at hm_1
        have left_is_even : Even (2 ^ (k + 1) * 2046) := by
          have even1: Even (2 ^ (k + 1)) := Even.pow_of_ne_zero (by simp : Even 2) (by simp : k + 1 ≠ 0)
          exact Even.mul_right even1 2046
        have right_is_odd : Odd ((2 * m + 1) * 2047) := by
          have odd1 : Odd (2 * m + 1) := by
            rw [odd_iff_exists_bit1]
            use m
          have odd2 : Odd (2047 : ℤ) := by
            rw [odd_iff_exists_bit1]
            use 1023
            norm_num
          exact Odd.mul odd1 odd2

        rw [<- hm_1] at right_is_odd
        norm_cast at right_is_odd
        contrapose right_is_odd
        simp
        exact left_is_even
      . have := pi_ne_zero
        contradiction

    -- Show that ∏(1 + 1/cos(2^k * θ₀)) = 1
    have h_prod_eq_one : (∏ k ∈ Finset.range 11, (1 + 1 / cos (2^k * θ₀))) = 1 := by
      -- Apply product formula to θ₀
      have prod_formula := product_formula θ₀ h_prod_cos_nonzero
      -- We need to show tan(2^10 * θ₀) / tan(θ₀ / 2) = 1

      -- First verify tan(2^10 * θ₀) = tan(θ₀ / 2)
      have tan_equal : tan (2^10 * θ₀) = tan (θ₀ / 2) := by
        -- θ₀ = 2046π/2047
        -- These differ by exactly 1023*π, making their tangents equal
        unfold θ₀
        field_simp
        ring_nf
        rw [(by ring : π * (2095104 / 2047) = π * (1023 / 2047) + 1023 * π)]
        exact tan_add_int_mul_pi (π * (1023 / 2047)) 1023

      -- From tan(2^10 * θ₀) = tan(θ₀ / 2), deduce the product equals 1
      have tan_nonzero : tan (θ₀ / 2) ≠ 0 := by
        have tan_pos: tan (θ₀ / 2) > 0 := by
          unfold θ₀
          apply tan_pos_of_pos_of_lt_pi_div_two
          . positivity
          . apply lt_of_sub_pos
            ring_nf
            positivity
        positivity

      have h_sin_nonzero : sin (θ₀ / 2) ≠ 0 := by
        rw [tan_eq_sin_div_cos] at tan_nonzero
        by_contra h_contra
        rw [h_contra] at tan_nonzero
        field_simp at tan_nonzero

      -- If tan(a) = tan(b) and tan(b) ≠ 0, then tan(a)/tan(b) = 1
      have : tan (2^10 * θ₀) / tan (θ₀ / 2) = 1 := by
        rw [tan_equal]
        exact div_self tan_nonzero

      have : (∏ k ∈ Finset.range 11, (1 + 1 / cos (2 ^ k * θ₀))) * sin (θ₀ / 2) / sin (θ₀ / 2) = 1 := by
        rw [prod_formula, ← this]
        nth_rw 3 [tan_eq_sin_div_cos]
        field_simp

      field_simp at this
      exact this

    -- Combine the results
    exact ⟨h_less_than_pi, h_prod_cos_nonzero, h_prod_eq_one⟩

  -- Combine results to show IsGreatest
  exact ⟨h_mem, h_upper⟩
