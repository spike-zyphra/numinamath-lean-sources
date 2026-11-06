import Mathlib

/- A certain function $f$ has the properties that $f(3x) = 3f(x)$ for all positive real values of $x$, and that $f(x) = 1 - |x - 2|$ for $1\leq x \leq 3$. Find the smallest $x$ for which $f(x) = f(2001)$. -/
theorem algebra_12626 {f : ℝ → ℝ} (h1 : ∀ x > 0, f (3 * x) = 3 * f x) (h2 : ∀ x ∈ Set.Icc 1 3, f x = 1 - |x - 2|) :
    IsLeast {x | x > 0 ∧ f x = f 2001} 429 := by
  have h1' : ∀ x > 0, f x = 3 * f (x / 3) := by
    intro x hx
    calc
      f x = f (3 * (x / 3)) := by rw [mul_comm]; norm_num
      _ = 3 * f (x / 3) := by rw [h1]; linarith only [hx]
  -- We first calculate the value of f(2001).
  have h2001 : f 2001 = 186 := by
    calc
      f 2001 = 3 * f (2001 / 3) := by rw [h1']; norm_num
      _ = 3 * (3 * f (2001 / 3 / 3)) := by rw [h1']; norm_num
      _ = 3 * (3 * (3 * f (2001 / 3 / 3 / 3))) := by rw [h1']; norm_num
      _ = 3 * (3 * (3 * (3 * f (2001 / 3 / 3 / 3 / 3)))) := by rw [h1']; norm_num
      _ = 3 * (3 * (3 * (3 * (3 * f (2001 / 3 / 3 / 3 / 3 / 3))))) := by rw [h1']; norm_num
      _ = 3 * (3 * (3 * (3 * (3 * (3 * f (2001 / 3 / 3 / 3 / 3 / 3 / 3)))))) := by rw [h1']; norm_num
      _ = 3 ^ 6 * f (2001 / 3 ^ 6) := by rw [<-mul_assoc, <-mul_assoc, <-mul_assoc, <-mul_assoc, <-mul_assoc]; norm_num
      _ = 3 ^ 6 * (1 - |2001 / 3 ^ 6 - 2|) := by rw [h2]; norm_num
      _ = 186 := by simp [abs]; norm_num
  rw [h2001]
  clear h2001
  -- We then calculate the value of f(429).
  have h429 : f 429 = 186 := by
    calc
      f 429 = 3 * f (429 / 3) := by rw [h1']; norm_num
      _ = 3 * (3 * f (429 / 3 / 3)) := by rw [h1']; norm_num
      _ = 3 * (3 * (3 * (f (429 / 3 / 3 / 3)))) := by rw [h1']; norm_num
      _ = 3 * (3 * (3 * (3 * (f (429 / 3 / 3 / 3 / 3))))) := by rw [h1']; norm_num
      _ = 3 * (3 * (3 * (3 * (3 * (f (429 / 3 / 3 / 3 / 3 / 3)))))) := by rw [h1']; norm_num
      _ = 3 ^ 5 * f (429 / 3 ^ 5) := by rw [<-mul_assoc, <-mul_assoc, <-mul_assoc, <-mul_assoc]; norm_num
      _ = 3 ^ 5 * (1 - |429 / 3 ^ 5 - 2|) := by rw [h2]; norm_num
      _ = 186 := by simp [abs]; norm_num
  -- We prove that f(x) ∈ [0, 3 ^ k] for any x ∈ [3 ^ k, 3 ^ (k + 1)], k ∈ ℕ.
  have h4 (k : ℕ) : ∀ x ∈ Set.Icc (3 ^ k) (3 ^ (k + 1)), f x ∈ Set.Icc 0 (3 ^ k) := by
    induction k with
    | zero =>
      rw [show 3 ^ 0 = (1 : ℝ) by norm_num, show 3 ^ (0 + 1) = (3 : ℝ) by norm_num]
      intro x hx
      rw [h2]
      simp [abs] at hx ⊢
      refine ⟨⟨?_, ?_⟩, ?_⟩
      . linarith [hx]
      . linarith [hx]
      . apply le_total 2 x
      exact hx
    | succ k hk =>
      intro x hx
      simp at hx ⊢
      rw [h1']
      suffices h : 0 ≤ f (x / 3) ∧ f (x / 3) ≤ 3 ^ k by
        refine ⟨?_, ?_⟩
        . linarith only [h]
        . rw [pow_add]
          linarith only [h]
      apply hk
      simp
      rw [pow_add, pow_add] at hx
      refine ⟨?_, ?_⟩
      . linarith only [hx]
      . linarith only [hx]
      calc
        x ≥ 3 ^ (k + 1) := by tauto
        _ > 0 := by rw [gt_iff_lt]; apply pow_pos; norm_num
  -- We prove that f(x) ∈ [0, 3 ^ (-k)] for any x ∈ [3 ^ (-k), 3 ^ (-k + 1)], k ∈ ℕ.
  have h5 (k : ℕ) : ∀ x ∈ Set.Icc (3 ^ (-k : ℤ)) (3 ^ (-k + 1 : ℤ)) , f x ∈ Set.Icc 0 (3 ^ (-k : ℤ)) := by
    induction k with
    | zero =>
      norm_cast
      rw [show 3 ^ (-0 : ℤ) = (1 : ℝ) by norm_num, show 3 ^ (-0 + 1 : ℤ) = (3 : ℝ) by norm_num]
      intro x hx
      rw [h2]
      simp [abs] at hx ⊢
      refine ⟨⟨?_, ?_⟩, ?_⟩
      . linarith [hx]
      . linarith [hx]
      . apply le_total 2 x
      exact hx
    | succ k hk =>
      intro x hx
      simp at hx ⊢
      suffices h : 0 ≤ 3 * f x ∧ 3 * f x ≤ 3 ^ (-k : ℤ) by
        refine ⟨?_, ?_⟩
        . linarith only [h]
        . calc
            f x = 3 * f x / 3 := by rw [mul_div_cancel_left₀]; norm_num
            _ ≤ (3 ^ (-k : ℤ) : ℝ) / 3 := by rw [div_le_div_right]; tauto; norm_num
            _ = 3 ^ (-k : ℤ) * 1 / 3 := by norm_num
            _ = 3 ^ (-1 + -k : ℤ) := by rw [zpow_add₀]; field_simp; rw [mul_comm]; norm_num
      rw [<-h1]
      apply hk
      simp [<-one_div] at hx ⊢
      rw [zpow_add₀] at hx
      refine ⟨?_, ?_⟩
      . rw [show 1 / 3 ^ k = (3 ^ (-k : ℤ) : ℝ) by simp]
        rw [show (3 ^ (-1 : ℤ) : ℝ) = 1 / 3 by norm_num] at hx
        linarith only [hx]
      . rw [zpow_add₀, mul_comm]
        simp [<-one_div]
        tauto
        norm_num
      norm_num
      calc
        x ≥ 3 ^ (-1 + -k : ℤ) := by tauto
        _ > 0 := by rw [gt_iff_lt]; apply zpow_pos_of_pos; norm_num
  -- Simp and break the goal, with f(429) = 186 solved above.
  simp [IsLeast, lowerBounds, h429]
  intro x xpos hx
  -- Case 1 : x < 1. Cannot find (contradiction).
  by_cases h6 : x < 1
  . let n : ℤ := -⌊(Real.logb 3 (1 / x) : ℝ)⌋
    have g₀ : 3 ^ (-n) ≤ 1 / x := by
      calc
        (3 ^ (-n) : ℝ) = 3 ^ (-n : ℝ) := by rw [Real.rpow_neg]; simp; norm_num
        _ ≤ 3 ^ (Real.logb 3 (1 / x) : ℝ) := by apply Real.rpow_le_rpow_of_exponent_le; norm_num; dsimp [n]; simp; apply Int.floor_le
        _ = 1 / x := by rw [Real.rpow_logb]; norm_num; norm_num; rw [one_div_pos]; exact xpos
    have g₁ : 1 / x < 3 ^ (-n + 1) := by
      calc
        (1 / x : ℝ) = 3 ^ (Real.logb 3 (1 / x) : ℝ) := by rw [Real.rpow_logb]; norm_num; norm_num; rw [one_div_pos]; exact xpos
        _ < 3 ^ (-n + 1 : ℝ) := by apply Real.rpow_lt_rpow_of_exponent_lt; norm_num; dsimp [n]; simp
        _ = (3 ^ (-n + 1) : ℝ) := by norm_cast
    have g₂ : -n ≥ 0 := by
      simp [n, -one_div]
      rw [Int.floor_nonneg]
      suffices g₂ : Real.logb 3 (1 / x) > 0 by
        linarith only [g₂]
      apply Real.logb_pos
      norm_num
      apply one_lt_one_div
      exact xpos
      exact h6
    specialize h5 ((-n + 1).natAbs) x
    rw [<-Int.eq_natAbs_of_zero_le] at h5
    rw [<-one_div_le_one_div, one_div_div, one_div, <-zpow_neg, show - -n = n by norm_num] at g₀
    rw [<-one_div_lt_one_div, one_div_div, one_div, <-zpow_neg] at g₁
    rw [show -(-n + 1) = n - 1 by ring_nf] at h5 g₁
    replace h5 : f x ∈ Set.Icc 0 (3 ^ (n - 1)) := by
      apply h5
      simp only [Set.Icc, Set.mem_setOf]
      refine ⟨?_, ?_⟩
      . linarith only [g₁]
      . simp
        linarith only [g₀]
    simp [hx] at h5
    absurd h5
    rw [not_le]
    calc
      (3 ^ (n - 1) : ℝ) ≤ 3 ^ (-1 : ℤ) := by rw [zpow_le_iff_le]; linarith only [g₂]; norm_num
      _ < 186 := by norm_num
    apply zpow_pos_of_pos
    norm_num
    rw [one_div_pos]
    exact xpos
    rw [one_div_pos]
    exact xpos
    apply zpow_pos_of_pos
    norm_num
    linarith only [g₂]
  . by_cases h7 : x < 3 ^ 5
    . -- Case 2 : 1 ≤ x < 3 ^ 5. Cannot find (contradiction).
      let n : ℤ := ⌊(Real.logb 3 x : ℝ)⌋
      have g₀ : 3 ^ n ≤ x := by
        calc
          (3 ^ n : ℝ) = 3 ^ (n : ℝ) := by norm_cast
          _ ≤ 3 ^ (Real.logb 3 x) := by apply Real.rpow_le_rpow_of_exponent_le; norm_num; dsimp [n]; apply Int.floor_le
          _ = x := by rw [Real.rpow_logb]; norm_num; norm_num; exact xpos
      have g₁ : x < 3 ^ (n + 1) := by
        calc
          x = 3 ^ (Real.logb 3 x) := by rw [Real.rpow_logb]; norm_num; norm_num; exact xpos
          _ < 3 ^ (n + 1 : ℝ) := by apply Real.rpow_lt_rpow_of_exponent_lt; norm_num; simp [n]
          _ = (3 ^ (n + 1) : ℝ) := by norm_cast
      have g₂ : n ≥ 0 := by
        simp [n]
        rw [Int.floor_nonneg]
        suffices g₂ : Real.logb 3 x ≥ 0 by
          linarith only [g₂]
        apply Real.logb_nonneg
        norm_num
        simp at h6
        exact h6
      have g₃ : n < 5 := by
        simp [n]
        rw [Int.floor_lt]
        calc
          Real.logb 3 x < Real.logb 3 (3 ^ 5) := by apply Real.logb_lt_logb; norm_num; assumption'
          _ = Real.logb 3 (3 ^ (5 : ℝ)) := by norm_cast
          _ = (5 : ℝ) := by rw [Real.logb_rpow]; norm_num; norm_num
      specialize h4 (n.natAbs)
      rw [show (3 ^ (n.natAbs) : ℝ) = 3 ^ n by rw [<-zpow_natCast, <-Int.eq_natAbs_of_zero_le]; apply g₂, show (3 ^ (n.natAbs + 1) : ℝ) = 3 ^ (n + 1) by rw [pow_add, <-zpow_natCast, zpow_add₀, <-Int.eq_natAbs_of_zero_le]; simp; apply g₂; norm_num] at h4
      replace h4 : f x ∈ Set.Icc 0 (3 ^ n) := by
        apply h4
        simp
        refine ⟨?_, ?_⟩
        . linarith only [g₀]
        . linarith only [g₁]
      simp [hx] at h4
      absurd h4
      simp
      calc
        (3 ^ n : ℝ) ≤ 3 ^ (4 : ℤ) := by rw [zpow_le_iff_le]; omega; norm_num
        _ < 186 := by norm_num
    . by_cases h8 : x < 3 ^ 6
      . -- Case 3 : 3 ^ 5 ≤ x < 3 ^ 6. The least value is 429.
        have g : f x = 3 ^ 5 * f (x / 3 ^ 5) := by
          calc
            f x = 3 * f (x / 3) := by rw [h1']; norm_num; exact xpos
            _ = 3 * (3 * f (x / 3 / 3)) := by rw [h1']; norm_num; exact xpos
            _ = 3 * (3 * (3 * (f (x / 3 / 3 / 3)))) := by rw [h1']; norm_num; exact xpos
            _ = 3 * (3 * (3 * (3 * (f (x / 3 / 3 / 3 / 3))))) := by rw [h1']; norm_num; exact xpos
            _ = 3 * (3 * (3 * (3 * (3 * (f (x / 3 / 3 / 3 / 3 / 3)))))) := by rw [h1']; norm_num; exact xpos
            _ = 3 ^ 5 * f (x / 3 ^ 5) := by rw [<-mul_assoc, <-mul_assoc, <-mul_assoc, <-mul_assoc]; field_simp; norm_num
        rw [h2 (x / 3 ^ 5), hx] at g
        replace g : |x / 3 ^ 5 - 2| = 19 / 81 := by
          linarith only [g]
        norm_num at g
        apply eq_or_eq_neg_of_abs_eq at g
        obtain g | g := g
        . field_simp at g
          nth_rewrite 2 [show (243 : ℝ) = 3 * 81 by norm_num] at g
          rw [<-mul_assoc] at g
          simp at g
          -- One solution is 543.
          have xeq : x = 543 := by
            linarith only [g]
          rw [xeq]
          norm_num
        . field_simp at g
          rw [show (-(19 * 243) : ℝ) = (-57) * 81 by norm_num] at g
          simp at g
          -- Another solution is 429.
          have xeq : x = 429 := by
            linarith only [g]
          rw [xeq]
        simp
        refine ⟨?_, ?_⟩
        . rw [one_le_div]
          linarith only [h7]
          norm_num
        . rw [div_le_iff₀]
          norm_num at h8 ⊢
          linarith only [h8]
          norm_num
      . -- Case 4 : x ≥ 3 ^ 6. Nothing to prove since x ≥ 429 is already satisfied.
        norm_num at h8
        calc
          x ≥ 729 := by apply h8
          _ ≥ 429 := by norm_num
