import Mathlib

open Real

/- 11. (NET) On a semicircle with unit radius four consecutive chords $A B, B C$, $C D, D E$ with lengths $a, b, c, d$, respectively, are given. Prove that  $$ a^{2}+b^{2}+c^{2}+d^{2}+a b c+b c d<4 $$ -/
theorem inequalities_23767 (θ₁ θ₂ θ₃ θ₄ : ℝ) (hpos : θ₁ > 0 ∧ θ₂ > 0 ∧ θ₃ > 0 ∧ θ₄ > 0) (hle : θ₁ + θ₂ + θ₃ + θ₄ ≤ π / 2) : (sin θ₁)^2 + (sin θ₂)^2 + (sin θ₃)^2 + (sin θ₄)^2 + 2*(sin θ₁)*(sin θ₂)*(sin θ₃) + 2*(sin θ₂)*(sin θ₃)*(sin θ₄) < 1 := by

-- STRATEGY: Use a substitution technique to create an equality case, then show strict inequality
-- Define θ₅ as the "remaining angle" to complete π/2
let θ₅ := π / 2 - (θ₁ + θ₂ + θ₃)

-- Since θ₁ + θ₂ + θ₃ + θ₄ ≤ π/2, we have θ₄ ≤ θ₅
have h1 : θ₄ ≤ θ₅ := by
  unfold θ₅
  linarith

-- By monotonicity of sine on [0, π/2], sin θ₄ ≤ sin θ₅
have h2 : sin θ₄ ≤ sin θ₅ := by
  apply sin_le_sin_of_le_of_le_pi_div_two
  linarith  -- θ₄ ≥ 0
  unfold θ₅
  linarith  -- θ₅ ≤ π/2
  linarith  -- θ₄ ≤ θ₅

-- KEY IDENTITY 1: When we group θ₁, θ₂ with (θ₃ + θ₅), we get a perfect identity
-- This represents the case where the four angles exactly sum to π/2
have h3 : (sin θ₁)^2 + (sin θ₂)^2 + (sin (θ₃+θ₅))^2 + 2*(sin θ₁)*(sin θ₂)*(sin (θ₃+θ₅)) = 1 := by
  -- Use the fact that θ₃ + θ₅ = π/2 - (θ₁ + θ₂)
  have : θ₃ + θ₅ = π / 2 - (θ₁ + θ₂) := by
    unfold θ₅
    ring
  -- Apply complementary angle identity: sin(π/2 - x) = cos(x)
  rw [this, sin_pi_div_two_sub]
  -- Use trigonometric identities to expand and simplify
  rw [Real.sin_sq_eq_half_sub, Real.sin_sq_eq_half_sub]
  calc
    _ = 1 - 1/2*(cos (2*θ₁)+cos (2*θ₂)) + (cos (θ₁+θ₂)*(cos (θ₁+θ₂) + 2*(sin θ₁)*(sin θ₂))) := by
      ring
    _ = 1 - 1/2 * (2 * cos (θ₁+θ₂)*(cos (θ₁-θ₂))) + cos (θ₁+θ₂)*(cos (θ₁-θ₂)) := by
      rw [Real.cos_add_cos]  -- Sum-to-product formula
      nth_rw 2 [Real.cos_add]
      have : cos θ₁ * cos θ₂ - sin θ₁ * sin θ₂ + 2 * sin θ₁ * sin θ₂ = cos (θ₁ - θ₂) := by
        ring_nf
        rw [Real.cos_sub]
      rw [this]
      ring_nf
    _ = _ := by ring

-- KEY IDENTITY 2: Similar identity with different grouping
have h4 : (sin θ₃)^2 + (sin θ₅)^2 + (sin (θ₁+θ₂))^2 + 2*(sin θ₃)*(sin θ₅)*(sin (θ₁+θ₂)) = 1 := by
  -- Use the fact that θ₁ + θ₂ = π/2 - (θ₃ + θ₅)
  have : θ₁ + θ₂ = π / 2 - (θ₃ + θ₅) := by
    unfold θ₅
    ring
  rw [this, sin_pi_div_two_sub (θ₃+θ₅)]
  -- Similar trigonometric manipulation as above
  rw [Real.sin_sq_eq_half_sub, Real.sin_sq_eq_half_sub]
  calc
    _ = 1 - 1/2*(cos (2*θ₃)+cos (2*θ₅)) + (cos (θ₃+θ₅)*(cos (θ₃+θ₅) + 2*(sin θ₃)*(sin θ₅))) := by
      ring
    _ = 1 - 1/2 * (2 * cos (θ₃+θ₅)*(cos (θ₃-θ₅))) + cos (θ₃+θ₅)*(cos (θ₃-θ₅)) := by
      rw [Real.cos_add_cos]
      nth_rw 2 [Real.cos_add]
      have : cos θ₃ * cos θ₅ - sin θ₃ * sin θ₅ + 2 * sin θ₃ * sin θ₅ = cos (θ₃ - θ₅) := by
        have : cos θ₃ * cos θ₅ - sin θ₃ * sin θ₅ + 2 * sin θ₃ * sin θ₅ = cos θ₃ * cos θ₅ + sin θ₃ * sin θ₅ := by ring
        rw [this]
        rw [← cos_sub]
      rw [this]
      ring_nf
    _ = _ := by  ring

-- AUXILIARY IDENTITY: Fundamental trigonometric identity
have h5 : (sin (θ₃+θ₅))^2 + (sin (θ₁+θ₂))^2 = 1 := by
  have : θ₃ + θ₅ = π / 2 - (θ₁ + θ₂) := by
    unfold θ₅
    ring
  rw [this, sin_pi_div_two_sub]
  exact cos_sq_add_sin_sq (θ₁ + θ₂)  -- cos²x + sin²x = 1

-- MONOTONICITY STEP: Replace θ₄ with θ₅ (which is larger) increases the expression
have h6 : sin θ₁ ^ 2 + sin θ₂ ^ 2 + sin θ₃ ^ 2 + sin θ₄ ^ 2 + 2*sin θ₁ * sin θ₂ * sin θ₃ + 2*sin θ₂ * sin θ₃ * sin θ₄ ≤ sin θ₁ ^ 2 + sin θ₂ ^ 2 + sin θ₃ ^ 2 + sin θ₅ ^ 2 + 2*sin θ₁ * sin θ₂ * sin θ₃ + 2*sin θ₂ * sin θ₃ * sin θ₅ := by
  -- Since sin θ₄ ≤ sin θ₅, we have (sin θ₄)² ≤ (sin θ₅)²
  have h1' : (sin θ₄)^2 ≤ (sin θ₅)^2 := by
    have : sin θ₄ > 0 := by
      apply sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have : sin θ₅ > 0 := by
      apply sin_pos_of_pos_of_lt_pi (by linarith)
      unfold θ₅
      linarith
    apply sq_le_sq' (by linarith) (by linarith)
  -- Since all sines are positive, sin θ₂ * sin θ₃ * sin θ₄ ≤ sin θ₂ * sin θ₃ * sin θ₅
  have h2' : sin θ₂ * sin θ₃ * sin θ₄ ≤ sin θ₂ * sin θ₃ * sin θ₅ := by
    have : sin θ₂ * sin θ₃ > 0 := by
      have : sin θ₂ > 0 := by apply sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      have : sin θ₃ > 0 := by apply sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      nlinarith
    exact (@mul_le_mul_left ℝ (sin θ₂ * sin θ₃) (sin θ₄) (sin θ₅) _ _ _ _ _ this).mpr h2
  linarith

-- STRICT INEQUALITY STEPS: Show that replacing individual terms with sums gives strict increases
-- sin θ₃ < sin(θ₃ + θ₅) since θ₅ > 0
have h7 : sin (θ₃) < sin (θ₃+θ₅) := by
  apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
  linarith  -- θ₃ < θ₃ + θ₅
  unfold θ₅
  linarith  -- θ₃ + θ₅ ≤ π/2
  linarith  -- θ₃ ≥ 0

-- sin θ₂ < sin(θ₁ + θ₂) since θ₁ > 0
have h8 : sin (θ₂) < sin (θ₁+θ₂) := by
  apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
  linarith  -- θ₂ < θ₁ + θ₂
  linarith  -- θ₁ + θ₂ ≤ π/2
  linarith  -- θ₂ ≥ 0

-- MAIN CALCULATION: Chain of inequalities leading to the final result
calc
  -- Start with the original expression
  _ ≤ sin θ₁ ^ 2 + sin θ₂ ^ 2 + sin θ₃ ^ 2 + sin θ₅ ^ 2 + 2*sin θ₁ * sin θ₂ * sin θ₃ + 2*sin θ₂ * sin θ₃ * sin θ₅ := by
    linarith  -- Apply h6: replace θ₄ with θ₅
  -- Apply strict inequalities from h7 and h8
  _ < sin θ₁ ^ 2 + sin θ₂ ^ 2 + sin θ₃ ^ 2 + sin θ₅ ^ 2 + 2*sin θ₁ * sin θ₂ * sin (θ₃+θ₅) + 2*sin (θ₁+θ₂) * sin θ₃ * sin θ₅ := by
    -- Since sin θ₁ * sin θ₂ > 0, multiplying by sin θ₃ < sin(θ₃ + θ₅) gives strict inequality
    have h9 : sin θ₁ * sin θ₂ * sin θ₃ < sin θ₁ * sin θ₂ * sin (θ₃ + θ₅) := by
      have : sin θ₁ * sin θ₂ > 0 := by
        have : sin θ₁ > 0 := by apply sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
        have : sin θ₂ > 0 := by apply sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
        nlinarith
      exact (@mul_lt_mul_left ℝ (sin θ₁ * sin θ₂) (sin θ₃) (sin (θ₃ + θ₅)) _ _ _ _ _ this).mpr h7
    -- Similarly for the second product term
    have h10 : sin θ₂ * sin θ₃ * sin θ₅ < sin (θ₁ + θ₂) * sin θ₃ * sin θ₅ := by
      rw [mul_assoc, mul_assoc]
      have : sin θ₃ * sin θ₅ > 0 := by
        have : sin θ₃ > 0 := by apply sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
        have : sin θ₅ > 0 := by
          apply sin_pos_of_pos_of_lt_pi (by linarith)
          unfold θ₅
          linarith
        nlinarith
      exact (@mul_lt_mul_right ℝ (sin θ₃ * sin θ₅) (sin θ₂) (sin (θ₁ + θ₂)) _ _ _ _ _ this).mpr h8
    linarith
  -- Rearrange terms to match the identities h3 and h4
  _ = (sin θ₁)^2 + (sin θ₂)^2 + (sin (θ₃+θ₅))^2 + 2*(sin θ₁)*(sin θ₂)*(sin (θ₃+θ₅)) + ((sin θ₃)^2 + (sin θ₅)^2 + (sin (θ₁+θ₂))^2 + 2*(sin θ₃)*(sin θ₅)*(sin (θ₁+θ₂))) - ((sin (θ₃+θ₅))^2 + (sin (θ₁+θ₂))^2) := by
    ring
  -- Apply the identities: both bracketed expressions equal 1, and the subtracted term also equals 1
  _ = 1 := by
    rw [h3, h4, h5]  -- Substitute the three key identities
    ring
