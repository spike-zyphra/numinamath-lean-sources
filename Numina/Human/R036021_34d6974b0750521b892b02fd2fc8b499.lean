import Mathlib

/- There are two values of a for which the equation 4x^2+ax+8x+9=0 has only one solution for x. What is the sum of these values of
(A) −16
(B) −8
(C) 0
(D) 8
(E) 20 -/
theorem algebra_97321 (a₁ a₂ : ℝ) (h_a_dist: a₁ ≠ a₂) (h : ∀ a:ℝ, (∃! x:ℝ, 4*x^2+a*x+8*x+9=0) ↔ (a = a₁ ∨ a = a₂)) : a₁ + a₂ = -16 := by
  -- first define identity and simple facts as we'll be using facts from quadratic
  have h_identity (y b:ℝ) : 4*y^2 + b*y + 8*y + 9 = 4*(y*y) + (b + 8)*y + 9 := by ring
  have h4 : (4:ℝ) ≠ 0 := by norm_num
  -- extract the fact that ∃! x:ℝ, 4*x^2+a*x+8*x+9=0 for a = a₁ and a = a₂
  have ha₁: ∃! x:ℝ, 4*x^2+a₁*x+8*x+9=0 := by
    apply (h a₁).mpr
    left
    rfl
  have ha₂: ∃! x:ℝ, 4*x^2+a₂*x+8*x+9=0 := by
    apply (h a₂).mpr
    right
    rfl
  -- now prove a lemma the ∃! x:ℝ, 4*x^2+a*x+8*x+9=0 implies discriminant (discrim 4 (a+8) 9) will be 0
  have h_discrim (a:ℝ) (h_unique: ∃! x:ℝ, 4*x^2+a*x+8*x+9=0) : discrim 4 (a+8) 9 = 0 := by
    obtain ⟨x, ⟨hx_val, hx_same⟩ ⟩ := h_unique
    simp at hx_same
    -- to prove it do either or on discrim 4 (a+8) 9 = s^2
    by_cases h : ∃ s: ℝ, discrim 4 (a+8) 9 = s^2
    -- if discrim 4 (a+8) 9 = s^2 then take the two root values and utilize the uniquness to prove both roots will be same
    . obtain ⟨s, hs⟩ := h
      rw [h_identity] at hx_val
      rw [pow_two s] at hs
      have x_two_val : x = (-(a + 8) + s) / (2 * 4) ∨ x = (-(a + 8) - s) / (2 * 4) := (quadratic_eq_zero_iff h4 hs x).mp hx_val
      have : (-(a + 8) + s) / ((2:ℝ) * 4) = (-(a + 8) - s) / ((2:ℝ) * 4) := by
        cases' x_two_val with hplus hminus
        . rw [← hplus]
          apply Eq.symm
          apply hx_same
          rw [h_identity]
          apply (quadratic_eq_zero_iff h4 hs _ ).mpr
          right
          rfl
        . rw [← hminus]
          apply hx_same
          rw [h_identity]
          apply (quadratic_eq_zero_iff h4 hs _ ).mpr
          left
          rfl
      -- if both are same then that will prove s = 0 so discrim 4 (a+8) 9 = 0
      have : s = 0 := by linarith
      rw [this] at hs
      linarith
    -- if not true then that will no solution exists, false
    . rw [not_exists] at h
      have h_no_x : 4*(x*x) + (a + 8)*x + 9 ≠ 0 := by exact quadratic_ne_zero_of_discrim_ne_sq h x
      rw [← h_identity] at h_no_x
      contradiction
  -- using the lemma prove discrim for both a₁ a₂ are 0
  have ha₁ : discrim 4 (a₁+8) 9 = 0 := by exact h_discrim a₁ ha₁
  have ha₂ : discrim 4 (a₂+8) 9 = 0 := by exact h_discrim a₂ ha₂
  -- factorize discrim expressions to ifind that a = -20 or a = 4
  have h_a_val (a:ℝ) (hd: discrim 4 (a+8) 9 = 0) : a = -20 ∨ a = 4 := by
    simp [discrim] at hd
    have : (a + 20) * (a - 4) = 0 := by
      calc
         (a + 20) * (a - 4) = (a + 8) ^ 2 - 4 * 4 * 9 := by ring
         _ = 0 := by rw [hd]
    cases' mul_eq_zero.mp this <;> first | (left; linarith) | (right; linarith)
  -- if a₁ = -20 or a₂ = 4 then do casework with the fact that a₁ ≠ a₂ to prove a₁ + a₂ = -16
  have ha₁ : a₁ = -20 ∨ a₁ = 4 := by exact h_a_val a₁ ha₁
  have ha₂ : a₂ = -20 ∨ a₂ = 4 := by exact h_a_val a₂ ha₂
  cases' ha₁ with ha_20 ha_4
  . rw [ha_20]
    have :a₂ ≠ -20 := by
      rw [ha_20] at h_a_dist
      exact h_a_dist.symm
    have :a₂ = 4 := by exact Or.resolve_left ha₂ this
    rw [this]
    norm_num
  . rw [ha_4]
    have :a₂ ≠ 4 := by
      rw [ha_4] at h_a_dist
      exact h_a_dist.symm
    have :a₂ = -20 := by exact Or.resolve_right ha₂ this
    rw [this]
    norm_num