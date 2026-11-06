import Mathlib

/- How many distinct ordered pairs of positive integers $(m,n)$ are there so that the sum of the reciprocals of $m$ and $n$ is $\frac14$? -/
theorem algebra_10697 :
    {(m, n) : ℕ × ℕ | m > 0 ∧ n > 0 ∧ (1 / m : ℚ) + (1 / n : ℚ) = 1 / 4}.ncard = 5 := by
  suffices h : {(m, n) : ℕ × ℕ | m > 0 ∧ n > 0 ∧ (1 / m : ℚ) + (1 / n : ℚ) = 1 / 4} = {(5, 20), (6, 12), (8, 8), (12, 6), (20, 5)} by
    rw [h]
    -- {(5, 20), (6, 12), (8, 8), (12, 6), (20, 5)} has cardinality 5.
    calc
      Set.ncard {(5, 20), (6, 12), (8, 8), (12, 6), (20, 5)} = Set.ncard {(6, 12), (8, 8), (12, 6), (20, 5)} + 1 := by rw [Set.ncard_insert_of_not_mem (by simp)]
      _ = Set.ncard {(8, 8), (12, 6), (20, 5)} + 1 + 1 := by rw [Set.ncard_insert_of_not_mem (by simp)]
      _ = Set.ncard {(12, 6), (20, 5)} + 1 + 1 + 1 := by rw [Set.ncard_insert_of_not_mem (by simp)]
      _ = Set.ncard {(20, 5)} + 1 + 1 + 1 + 1 := by rw [Set.ncard_insert_of_not_mem (by simp)]
      _ = 1 + 1 + 1 + 1 + 1 := by rw [Set.ncard_singleton]
      _ = 5 := by norm_num
  ext x
  -- Break the iff into two parts.
  apply Iff.intro <;> intro h
  . -- If (m, n) satisfies, then (m, n) belongs to one of the five values.
    simp
    obtain ⟨h₀, h₁, h₂⟩ := h
    field_simp at h₂
    replace h₂ : (x.1 - 4 : ℚ) * (x.2 - 4) = 16 := by
      calc
        (x.1 - 4 : ℚ) * (x.2 - 4) = x.1 * x.2 - 4 * x.1 - 4 * x.2 + 16 := by ring_nf
        _ = (x.2 + x.1) * 4 - 4 * x.1 - 4 * x.2 + 16 := by rw [<-h₂]
        _ = 16 := by ring_nf
    have h₃ : x.1 > 4 := by
      by_contra!
      by_cases h₃ : x.1 = 4
      . -- When m = 4, impossible.
        rw [h₃] at h₂
        norm_cast at h₂
        rw [Int.subNatNat_self, zero_mul] at h₂
        omega
      . -- When m < 4, we have n < 4, impossible.
        have h₄ : 0 < (x.1 - 4 : ℚ) * (x.2 - 4) := by
          rw [h₂]
          norm_num
        apply neg_of_mul_pos_right at h₄
        simp at h₄
        replace h₃ : x.1 < 4 := by
          omega
        apply h₄ at this
        clear h₄
        -- List all cases of m < 4, n < 4, and prove that each is impossible.
        interval_cases x.1 <;> interval_cases x.2
        all_goals
          simp at h₂
          linarith
    have h₄ : 0 < (x.1 - 4 : ℚ) * (x.2 - 4) := by
      rw [h₂]
      norm_num
    rw [mul_pos_iff_of_pos_left (by simp; omega)] at h₄
    replace h₄ : x.2 > 4 := by
      qify
      linarith
    have g₀ : (x.1 - 4 : ℕ) = (x.1 - 4 : ℚ) := by
      norm_cast
      rw [Int.subNatNat_of_le]
      omega
    have g₁ : (x.2 - 4 : ℕ) = (x.2 - 4 : ℚ) := by
      norm_cast
      rw [Int.subNatNat_of_le]
      omega
    rw [<-g₀, <-g₁] at h₂
    clear g₀ g₁
    norm_cast at h₂
    -- Now we have (m - 4) * (n - 4) = 16.
    let z : ℕ × ℕ := (x.1 - 4, x.2 - 4)
    have h₅ : z.1 * z.2 = 16 ∧ 16 ≠ 0 := by
      simp
      exact h₂
    rw [<-Nat.mem_divisorsAntidiagonal] at h₅
    -- Use the computer to find the factors of 16 (native_decide is necessary).
    rw [show Nat.divisorsAntidiagonal 16 = {(1, 16), (2, 8), (4, 4), (8, 2), (16, 1)} by native_decide] at h₅
    simp at h₅
    have h₆ : z = (x.1 - 4, x.2 - 4) := by
      simp
    have lm {a b : ℕ} (x z : ℕ × ℕ) (h₀ : z = (x.1 - 4, x.2 - 4)) (h₁ : z = (a, b)) (h₂ : x.1 > 4) (h₃ : x.2 > 4) : x = (a + 4, b + 4) := by
      calc
        x = (x.1, x.2) := by simp
        _ = (x.1 - 4 + 4, x.2 - 4 + 4) := by rw [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)]
        _ = (z.1 + 4, z.2 + 4) := by rw [h₀]
        _ = (a + 4, b + 4) := by rw [h₁]
    obtain g | g | g | g | g := h₅
    all_goals
      apply lm x z h₆ at g
      norm_num at g
      tauto
  . -- If (m, n) belongs to one of the five values, then it satisfies the equation.
    simp at h ⊢
    obtain g | g | g | g | g := h
    all_goals
      simp [g]
      norm_num
