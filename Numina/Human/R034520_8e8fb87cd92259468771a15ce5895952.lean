import Mathlib
open Real

/- The minimum positive period of the function $y=\cos ^{2}x-\sin ^{2}x$ is $T=$ _____ . -/
theorem algebra_9154 {f : ℝ → ℝ} (hf : f = λ x => cos x ^ 2 - sin x ^ 2) :
    IsLeast {T | 0 < T ∧ f = λ x => f (x + T)} π := by
  -- Rewrite the function as cos 2x
  conv_rhs at hf =>
    ext x
    rw [← cos_two_mul']

  -- We have two goals:
  -- 1. π is a positive period of the function
  -- 2. Any positive period of the function is at least π
  simp [hf, IsLeast, lowerBounds]
  constructor

  . -- π is a positive period of the function
    refine ⟨pi_pos, ?_⟩
    ext x
    -- We need to prove cos 2(x + π) = cos 2x
    -- This is true because cos is periodic with period 2π
    rw [mul_add]
    simp

  . -- Any positive period of the function is at least π
    intro T Tpos hT
    -- If T is a positive period of the function, then cos 2T = cos 0 = 1
    apply_fun (· 0) at hT
    simp at hT
    symm at hT
    -- 2T = 2nπ for some integer n
    rw [cos_eq_one_iff] at hT
    obtain ⟨n, hn⟩ := hT

    -- We have n > 0, and thus n ≥ 1
    -- We need to coerce n between ℝ and ℕ
    have npos : n > (0 : ℝ) := by nlinarith [pi_pos]
    replace npos : (n : ℝ) > (0 : ℕ) := by simp [npos]
    replace npos : n > 0 := Int.cast_lt.1 npos
    replace npos : n ≥ 1 := by omega
    replace npos : (n : ℝ) ≥ (1 : ℕ) := Int.cast_le.2 npos

    -- T ≥ π
    simp at npos
    nlinarith [pi_pos]
