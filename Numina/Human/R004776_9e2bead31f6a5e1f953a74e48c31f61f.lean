import Mathlib
set_option maxHeartbeats 300000

/- Four, (50 points) Let positive integers $a, b$, such that $\frac{(a+b)^{2}}{4 a b+1}$ is an integer. Prove: $\frac{(a+b)^{2}}{4 a b+1}$ is a perfect square. -/
theorem number_theory_321627 (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (h : ∃ k : ℕ, (a + b) ^ 2 / (4 * a * b + 1 : ℝ) = k) :
    ∃ m : ℕ, m ^ 2 = (a + b) ^ 2 / (4 * a * b + 1 : ℝ) := by
  -- Let k = (a + b) ^ 2 / (4 * a * b + 1).
  obtain ⟨k, hk⟩ := h
  -- WLOG, assume that a > b.
  wlog h₀ : a > b
  . -- Show that a ≠ b.
    have h₁ : a ≠ b := by
      -- Assume on the contrary that a = b.
      intro hab
      simp [<-hab] at hk
      replace hk := congr_arg (1 - ·) hk
      simp only at hk
      rw [one_sub_div (by positivity)] at hk
      ring_nf at hk
      rw [<-one_div] at hk
      field_simp at hk
      -- This would give k < 1, so k = 0, contradiction.
      have hk' : k < 1 := by
        rify
        nlinarith
      simp at hk'
      simp [hk'] at hk
      simp [hk] at ha
    -- Use the assumption.
    specialize this b a hb ha k (by rw [<-hk]; ac_rfl) (by contrapose h₁; simp; linarith)
    rw [add_comm, mul_assoc, mul_comm (a : ℝ) b, <-mul_assoc]
    exact this
  . -- Now we can assume that a > b.
    clear ha
    -- Consider the set of all such (a, b) such that (a + b)² / (4ab + 1) = k.
    let S := {x | ∃ a b : ℕ, 0 < b ∧ b < a ∧ (a + b) ^ 2 / (4 * a * b + 1 : ℝ) = k ∧ x = a + b}
    have h₁ : S.Nonempty := by
      use a + b
      simp [S]
      use a, b
    -- Now S contains a minimal element, called x₀.
    set x₀ := sInf S with hx₁
    have h₂ : x₀ ∈ S := by
      exact Nat.sInf_mem h₁
    simp [S] at h₂
    -- Let (a₀, b₀) with 0 < b₀ < a₀ such that (a₀ + b₀)² / (4 a₀b₀ + 1) = k and x₀ = a₀ + b₀.
    obtain ⟨a₀, b₀, hb₀, hab₀, h₂, hx₀⟩ := h₂
    rw [hk]
    replace hk := h₂
    field_simp at h₂
    -- Rewrite the equation as quadratic equation in a₀.
    replace h₂ : (a₀ * a₀ - (4 * k * b₀ - 2 * b₀) * a₀ + (b₀ ^ 2 - k) : ℝ) = 0 := by
      linarith
    -- Let a₁ be the another solution of this quadratic equation.
    have ⟨a₁, h₃, h₄, h₅⟩ := vieta_formula_quadratic h₂
    -- We shall show that k = b₀² is a perfect square.
    use b₀
    -- Assume on the contrary that b₀² > k or b₀² < k.
    by_contra! h₆
    rw [ne_iff_lt_or_gt] at h₆
    rcases h₆ with (h₆ | h₆)
    . -- Show that a₁ < 0 by a₀a₁ = b₀² - k < 0.
      have h₇ : a₁ < 0 := by
        nlinarith
      -- We have a₀ > 0.
      have h₈ : a₀ > 0 := by
        nlinarith
      -- Note that a₁ can be expressed as an integer, and hence a natural number.
      let a₁' : ℤ := 4 * k * b₀ - 2 * b₀ - a₀
      have h₉ : a₁' = a₁ := by
        simp [a₁']
        linarith
      replace h₇ : a₁ ≤ -1 := by
        rw [<-h₉] at h₇ ⊢
        norm_cast at h₇ ⊢
        simp
        omega
      -- We have (b₀² - k) / a₀ = a₁ ≤ -1.
      have h₁₀ : (b₀ ^ 2 - k) / a₀ = a₁ := by
        field_simp
        linarith
      replace h₁₀ : (b₀ ^ 2 - k) / a₀ ≤ (-1 : ℝ) := by
        rw [h₁₀]
        exact h₇
      -- Therefore, k ≥ b₀² + a₀.
      rw [div_le_iff₀' (by simp [h₈])] at h₁₀
      replace h₁₀ : k ≥ b₀ ^ 2 + a₀ := by
        rify
        linarith
      -- We get a contradiction a₀ + 2b₀ > a₀ + 2b₀.
      have h₁₁ : a₀ + 2 * b₀ > a₀ + 2 * b₀ := by
        calc
          _ > (4 * a₀ + 4 * b₀ ^ 2) * b₀ := by
            suffices a₀ > (4 * (b₀ ^ 2 + a₀) * b₀ - 2 * b₀ : ℝ) by
              rify
              linarith
            calc
              _ > (4 * k * b₀ - 2 * b₀ : ℝ) := by
                linarith
              _ ≥ 4 * (b₀ ^ 2 + a₀) * b₀ - 2 * b₀ := by
                simp
                rw [mul_le_mul_iff_of_pos_right (by positivity), mul_le_mul_iff_of_pos_left (by norm_num)]
                norm_cast
          _ ≥ 4 * a₀ + 4 * b₀ ^ 2 := by
            nlinarith
          _ > a₀ + 2 * b₀ := by
            apply Nat.add_lt_add
            . linarith
            . nlinarith
      -- This is clearly absurd.
      absurd h₁₁
      simp
    . -- Show that a₁ > 0 by a₀a₁ = b₀² - k > 0.
      have h₇ : a₁ > 0 := by
        nlinarith
      -- Show that a₀a₁ < a₀².
      replace h₅ : a₀ * a₁ < a₀ ^ 2 := by
        calc
          _ = (b₀ ^ 2 - k : ℝ) := h₅
          _ < b₀ ^ 2 := by
            simp
            -- Prove that 0 < k by contradiction.
            by_contra! h₈
            simp at h₈
            simp [h₈] at hk
            rcases hk with (hk | hk)
            all_goals
              absurd hk
              positivity
          _ < (a₀ ^ 2 : ℝ) := by
            norm_cast
            nlinarith
      -- We have a₁ < a₀.
      replace h₅ : a₁ < a₀ := by
        nlinarith
      -- Note that a₁ can be expressed as an integer, and hence a natural number.
      let a₁' : ℤ := 4 * k * b₀ - 2 * b₀ - a₀
      have h₈ : a₁' = a₁ := by
        simp [a₁']
        linarith
      let a₁'' : ℕ := a₁'.natAbs
      have h₉ : a₁'' = a₁' := by
        rw [Int.natAbs_of_nonneg]
        rify
        rw [h₈]
        exact le_of_lt h₇
      rw [<-h₉] at h₈
      -- This contradicts the minimality of x₀, because a₁ + b₀ < a₀ + b₀ = x₀.
      have h₁₀ : a₁'' + b₀ ∈ S := by
        simp [S]
        -- Show that b₀ ≠ a₁''.
        have hab₁ : b₀ ≠ a₁'' := by
          -- Assume on the contrary that b₀ = a₁'', we derive a contradiction.
          by_contra! hab₁
          rw [<-h₈, <-hab₁] at h₃
          simp at h₃
          ring_nf at h₃
          replace h₃ : (4 * b₀ ^ 2 + 1) * (1 - k : ℝ) = 1 := by
            linarith
          simp at h₃
          -- This would give k < 1, so k = 0, contradiction.
          have hk' : k < 1 := by
            rify
            nlinarith
          simp at hk'
          simp [hk'] at hk
          rcases hk with (hk | hk)
          all_goals
            absurd hk
            positivity
        by_cases hab₂ : b₀ < a₁''
        . -- Suppose b₀ < a₁'', we show that (a₁'', b₀) satisfies the condition.
          use a₁'', b₀
          refine ⟨hb₀, hab₂, ?_, by rfl⟩
          -- Show that (a₁'' + b₀)² / (4 * a₁'' * b₀ + 1) = k.
          field_simp
          simp [<-h₈] at h₃
          linarith
        . -- Suppose a₁'' < b₀, we show that (b₀, a₁'') satisfies the condition.
          push_neg at hab₂
          replace hab₂ := lt_of_le_of_ne hab₂ hab₁.symm
          use b₀, a₁''
          refine ⟨?_, hab₂, ?_, by ac_rfl⟩
          . simp [<-h₈] at h₇
            exact h₇
          . -- Show that (b₀ + a₁'')² / (4 * b₀ * a₁'' + 1) = k.
            field_simp
            simp [<-h₈] at h₃
            linarith
      -- This contradicts the minimality of x₀.
      have h₁₁ := Nat.sInf_le h₁₀
      rw [<-hx₁] at h₁₁
      simp [<-h₈] at h₅
      linarith
