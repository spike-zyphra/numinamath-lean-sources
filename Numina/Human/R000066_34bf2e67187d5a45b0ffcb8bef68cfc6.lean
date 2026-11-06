import Mathlib

open Real Int Nat

-- NOTICE: In Mathlib, floor is not defined **directly** in `Real`.

-- See:
#check exists_floor

/- Let $\lfloor x \rfloor$ denote the floor function of $x$, which is the greatest integer less than or equal to $x$. Given an integer $n$, show that : 
$$
\lfloor \sqrt{n} + \sqrt {n+1} \rfloor = \lfloor\sqrt {4n +2} \rfloor
$$
-/
theorem algebra_4207 {n : ℕ} : ¬∃ k : ℤ, √n + √(n+1) < k ∧ k ≤ √(4*n + 2) := by
  -- by contradiction, assume that there exists an integer k such that 
  -- $\sqrt n + \sqrt {n + 1} < k \le \sqrt {4n+2}$
  by_contra h
  rcases h with ⟨k, h₁, h₂⟩
  have h' : (√n + √(n+1))^2 < k^2 := by
    apply pow_lt_pow_left h₁
    apply add_nonneg (Real.sqrt_nonneg n) (Real.sqrt_nonneg (n+1))
    linarith
  have hkpos : 0 < (k : ℝ) := by
    have : 0 < √n + √(n+1) := by
      apply add_pos_of_nonneg_of_pos (Real.sqrt_nonneg n) (Real.sqrt_pos.mpr (by linarith))
    apply lt_trans this h₁
  have : (√n + √(n+1))^2 = 2*n + 1 + 2*√(n*(n+1)) := by
    rw [add_sq]
    norm_num
    rw [Real.sq_sqrt (by linarith)]
    ring_nf
  rw [this] at h'
  -- consider the second part of the assumption $k \le \sqrt {4n+2}$, squaring this yields : $k^2 \le 4n+2$.
  have h'' : (k^2 : ℝ) ≤ 4*n + 2 := by
    rw [← Real.sqrt_sq (show 0 ≤ (k : ℝ) by nlinarith)] at h₂
    apply (Real.sqrt_le_sqrt_iff (show 0 ≤ (4*n + 2 : ℝ) by nlinarith)).mp h₂
  have : n ≤ √(n*(n+1)) := by
    nth_rw 1 [← Real.sqrt_sq (show 0 ≤ (n : ℝ) by linarith)]
    rw [Real.sqrt_le_sqrt_iff (show 0 ≤ (n * (n + 1) : ℝ) by nlinarith)]
    nlinarith
  -- Apply the inequality chain we get $4n+1 < k^2 \le 4n+2$
  have h' : 4*n + 1 < (k^2 : ℝ) := by linarith
  have : 4*n + 2 ≤ (k^2 : ℝ) := by norm_cast at *
  -- the only integer in this interval is precisely $4n+2$.
  have hkn : (k^2 : ℝ) = 4*n + 2 := by nlinarith
  have hkn' : k^2 = 4*n + 2 := by norm_cast at hkn
  have h₀ : (4*n + 2) % 4 = (2 : ℤ) := by
    norm_cast
    rw [add_comm,Nat.add_mul_mod_self_left]
  rw [← hkn'] at h₀
  have : _ := Int.sq_ne_two_mod_four k
  rw [(show k * k = k^2 by ring)] at this
  exact this h₀
