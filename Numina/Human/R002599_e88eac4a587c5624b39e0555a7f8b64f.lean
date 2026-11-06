import Mathlib

/-- For any sequence of real numbers A=(a1,a2,a3,…), let ΔA​
    be the sequence (a2−a1,a3−a2,a4−a3,…) whose n-th​ term is a(n+1)−a(n).
    Suppose that all of the terms of the sequence Δ(ΔA) are 1​, and that a19=a92=0. Find a1​. -/
theorem algebra_96041 {a : ℕ → ℝ} (Δ : (ℕ → ℝ) → (ℕ → ℝ)) (hΔ : ∀ a n, Δ a n = a (n + 1) - (a n))
    (ha : ∀ n, Δ (Δ a) n = 1)
    (h18 : a 18 = 0) (h91 : a 91 = 0) : a 0 = 819 := by
  -- Note that all terms have to be offset by one due to Lean naturals starting at 0.
  conv at ha =>
    intro n
    rw[hΔ, hΔ, hΔ]
  -- From the conditions, we have a(n-1) + a(n+1) = 2 a(n) + 1 for n >= 1.
  convert_to ∀ n, a (n+2) = 2 * a (n + 1) + 1 - a n using 0 at ha
  · apply forall_congr'
    intro n
    rw[sub_eq_iff_eq_add', sub_eq_iff_eq_add']
    ring_nf
  -- Let a' = a(0), b' = a(1).
  let a' := a 0
  let b' := a 1
  -- From this, we get a(n) = n * b' + (n-1) * n / 2 - (n-1) * a' by induction.
  have a_shape : ∀ n, a (n + 2) = (n + 2) * b' + (n + 1) * (n + 2) / (2 : ℝ) - (n + 1) * a' := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => rw[ha]; ring
    | one => rw[ha, ha]; ring
    | more n ih1 ih2 =>
      rw[ha, ih1, ih2]
      field_simp
      ring
  -- Specialize this statement to n = 18, this yields 0 = 18 * b' + 153 - 17 * a',
  have a18 : 0 = 18 * b' + 153 - 17 * a' := by
    rw[← h18]
    convert a_shape 16 <;> norm_num
  -- and specialized to n = 91 it yields 0 = 91 b' + 45 * 91 - 90 * a'.
  have a91 : 0 = 91 * b' + 45 * 91 - 90 * a' := by
    rw[← h91]
    convert a_shape 89 using 1
    norm_num
  -- Hence (b' = 90 * a' - 45 * 91)/91
  have : b' = (90 * a' - 45 * 91)/91 := by linarith
  -- which we can insert in the first equation
  rw[this] at a18
  -- and finally solve the resulting linear equation for a' = 819.
  have : a' = 819 := by linarith
  exact this