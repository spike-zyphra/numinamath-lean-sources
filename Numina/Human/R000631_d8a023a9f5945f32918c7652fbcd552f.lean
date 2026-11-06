import Mathlib

/- Find $3x^2 y^2$ if $x$ and $y$ are integers such that $y^2 + 3x^2 y^2 = 30x^2 + 517$. -/
theorem number_theory_13443 (x y : ℤ) (h : y ^ 2 + 3 * x ^ 2 * y ^ 2 = 30 * x ^ 2 + 517) :
    3 * x ^ 2 * y ^ 2 = 588 := by
  -- Factorize the expression at LHS of h.
  replace h : (3 * x ^ 2 + 1) * (y ^ 2 - 10) = 507 := by
    linarith only [h]
  -- We compare the factorization with the possible integer factorization of 507.
  -- Let z = (3x² + 1, y² - 10).
  let z : ℕ × ℕ := (Int.natAbs (3 * x ^ 2 + 1), Int.natAbs (y ^ 2 - 10))
  -- Note that 3 * x ^ 2 + 1 ≥ 0, so we also have y ^ 2 - 10 ≥ 0.
  have h₀ : 3 * x ^ 2 + 1 ≥ 0 := by
    positivity
  have h₁ : y ^ 2 - 10 ≥ 0 := by
    nlinarith only [h, h₀]
  replace h₀ : 3 * x ^ 2 + 1 = Int.natAbs (3 * x ^ 2 + 1) := by
    apply Int.eq_natAbs_of_zero_le
    exact h₀
  replace h₁ : y ^ 2 - 10 = Int.natAbs (y ^ 2 - 10) := by
    apply Int.eq_natAbs_of_zero_le
    exact h₁
  rw [h₀, h₁] at h
  norm_cast at h
  have hz : z.1 * z.2 = 507 ∧ 507 ≠ 0 := by
    refine ⟨?_, ?_⟩
    . dsimp [z]
      exact h
    . norm_num
  rw [<-Nat.mem_divisorsAntidiagonal] at hz
  -- Use the computer to find the factors of 507 (native_decide is necessary).
  rw [show Nat.divisorsAntidiagonal 507 = {(1, 507), (3, 169), (13, 39), (39, 13), (169, 3), (507, 1)} by native_decide] at hz
  simp at hz
  -- We try each possibility.
  obtain hz | hz | hz | hz | hz | hz := hz
  . -- Suppose z = (1, 507). Impossible.
    replace h₁ : y ^ 2 - 10 = 507 := by
      calc
        y ^ 2 - 10 = z.2 := by dsimp [z]; exact h₁
        _ = 507 := by rw [hz]; simp
    have h₂ : 22 ^ 2 < |y| ^ 2 := by
      simp
      omega
    replace h₁ : |y| ^ 2 < 23 ^ 2 := by
      simp
      omega
    replace h₂ : 22 < |y| := by
      rw [sq_lt_sq] at h₂
      simp at h₂
      exact h₂
    replace h₁ : |y| < 23 := by
      rw [sq_lt_sq] at h₁
      simp at h₁
      exact h₁
    omega
  . -- Suppose z = (3, 169). Impossible.
    replace h₁ : y ^ 2 - 10 = 169 := by
      calc
        y ^ 2 - 10 = z.2 := by dsimp [z]; exact h₁
        _ = 169 := by rw [hz]; simp
    have h₂ : 13 ^ 2 < |y| ^ 2 := by
      simp
      omega
    replace h₁ : |y| ^ 2 < 14 ^ 2 := by
      simp
      omega
    replace h₂ : 13 < |y| := by
      rw [sq_lt_sq] at h₂
      simp at h₂
      exact h₂
    replace h₁ : |y| < 14 := by
      rw [sq_lt_sq] at h₁
      simp at h₁
      exact h₁
    omega
  . -- Suppose z = (13, 39). We get the desird answer.
    replace h₁ : y ^ 2 - 10 = 39 := by
      calc
        y ^ 2 - 10 = z.2 := by dsimp [z]; exact h₁
        _ = 39 := by rw [hz]; simp
    replace h₁ : |y| ^ 2 = 7 ^ 2 := by
      simp
      omega
    have h₂ : 3 * x ^ 2 + 1 = 13 := by
      calc
        3 * x ^ 2 + 1 = z.1 := by dsimp [z]; exact h₀
        _ = 13 := by rw [hz]; simp
    replace h₂ : |x| ^ 2 = 2 ^ 2 := by
      simp
      omega
    rw [sq_eq_sq] at h₁ h₂
    rw [show x ^ 2 = |x| ^ 2 by simp, show y ^ 2 = |y| ^ 2 by simp, h₁, h₂]
    all_goals
      norm_num
  . -- Suppose z = (39, 13). Impossible.
    replace h₁ : y ^ 2 - 10 = 13 := by
      calc
        y ^ 2 - 10 = z.2 := by dsimp [z]; exact h₁
        _ = 13 := by rw [hz]; simp
    have h₂ : 4 ^ 2 < |y| ^ 2 := by
      simp
      omega
    replace h₁ : |y| ^ 2 < 5 ^ 2 := by
      simp
      omega
    replace h₂ : 4 < |y| := by
      rw [sq_lt_sq] at h₂
      simp at h₂
      exact h₂
    replace h₁ : |y| < 5 := by
      rw [sq_lt_sq] at h₁
      simp at h₁
      exact h₁
    omega
  . -- Suppose z = (169, 3). Impossible.
    replace h₁ : y ^ 2 - 10 = 3 := by
      calc
        y ^ 2 - 10 = z.2 := by dsimp [z]; exact h₁
        _ = 3 := by rw [hz]; simp
    have h₂ : 3 ^ 2 < |y| ^ 2 := by
      simp
      omega
    replace h₁ : |y| ^ 2 < 4 ^ 2 := by
      simp
      omega
    replace h₂ : 3 < |y| := by
      rw [sq_lt_sq] at h₂
      simp at h₂
      exact h₂
    replace h₁ : |y| < 4 := by
      rw [sq_lt_sq] at h₁
      simp at h₁
      exact h₁
    omega
  . -- Suppose z = (507, 1). Impossible.
    replace h₁ : y ^ 2 - 10 = 1 := by
      calc
        y ^ 2 - 10 = z.2 := by dsimp [z]; exact h₁
        _ = 1 := by rw [hz]; simp
    have h₂ : 3 ^ 2 < |y| ^ 2 := by
      simp
      omega
    replace h₁ : |y| ^ 2 < 4 ^ 2 := by
      simp
      omega
    replace h₂ : 3 < |y| := by
      rw [sq_lt_sq] at h₂
      simp at h₂
      exact h₂
    replace h₁ : |y| < 4 := by
      rw [sq_lt_sq] at h₁
      simp at h₁
      exact h₁
    omega
