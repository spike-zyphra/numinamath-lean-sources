import Mathlib

/- Proof of 1ER: If $x, y, z$ are distinct integers, and $n$ is a non-negative integer, then
$$
\frac{x^{n}}{(x-y)(x-z)}+\frac{y^{n}}{(y-x)(y-z)}+\frac{z^{n}}{(z-x)(z-y)}
$$
is an integer. -/
theorem algebra_178712 {x y z : ℤ} (hxyz : x ≠ y ∧ y ≠ z ∧ x ≠ z) (n : ℕ) :
    ∃ k : ℤ, x ^ n / ((x - y) * (x - z) : ℚ) + y ^ n / ((y - x) * (y - z) : ℚ) +
      z ^ n / ((z - x) * (z - y) : ℚ) = k := by
  -- Denote the expression in the goal as s(n).
  set s : ℕ → ℚ := fun n => x ^ n / ((x - y) * (x - z) : ℚ) + y ^ n / ((y - x) * (y - z) : ℚ) +
      z ^ n / ((z - x) * (z - y) : ℚ) with s_eq
  -- We need to show that s(n) ∈ ℤ for all n.
  rw [← congr_fun s_eq n]
  -- Let a = x + y + z ∈ ℤ.
  set a := x + y + z
  -- Let b = x * y + y * z + z * x ∈ ℤ.
  set b := x * y + y * z + z * x
  -- Let c = x * y * z ∈ ℤ.
  set c := x * y * z
  have h0 : (x - y : ℚ) ≠ 0 ∧ (y - x : ℚ) ≠ 0 ∧ (x - z : ℚ) ≠ 0 ∧ (z - x : ℚ) ≠ 0 ∧ (y - z : ℚ) ≠ 0 ∧ (z - y : ℚ) ≠ 0 := by
    norm_cast
    omega
  -- s(k) can be written as
  -- s(k) = (x ^ k * (y - z) - y ^ k * (x - z) + z ^ k * (x - y)) / ((x - y) * (x - z) * (y - z)).
  have hs k : s k = (x ^ k * (y - z) - y ^ k * (x - z) + z ^ k * (x - y)) / ((x - y) * (x - z) * (y - z)) := by
    dsimp [s]
    field_simp [h0]
    ring
  -- We compute s(0) = 0.
  have hs0 : s 0 = 0 := by simp [hs]
  -- We compute s(1) = 0.
  have hs1 : s 1 = 0 := by
    simp [hs]
    left
    ring
  -- We compute s(2) = 1.
  have hs2 : s 2 = 1 := by
    field_simp [hs, h0]
    ring
  -- Prove the following formula:
  -- s (k + 3) = a * s (k + 2) - b * s (k + 1) + c * s k
  have hs_rec (k : ℕ) : s (k + 3) = a * s (k + 2) - b * s (k + 1) + c * s k := by
    -- Expand the definitions of s, a, b, c and simplify the expression to get the result.
    field_simp [hs, h0, a, b, c]
    ring
  -- Show that s(k) ∈ ℤ for all k.
  let rec h : (k : ℕ) → ∃ z : ℤ, s k = z
  -- s(0) = 0 ∈ ℤ.
  | 0 => by use 0; simp [hs0]
  -- s(1) = 0 ∈ ℤ.
  | 1 => by use 0; simp [hs1]
  -- s(2) = 1 ∈ ℤ.
  | 2 => by use 1; simp [hs2]
  | k + 3 => by
    -- Consider k + 3.
    -- We have s(k) = z0 ∈ ℤ, s(k + 1) = z1 ∈ ℤ, s(k + 2) = z2 ∈ ℤ.
    have ⟨z0, hz0⟩ := h k
    have ⟨z1, hz1⟩ := h (k + 1)
    have ⟨z2, hz2⟩ := h (k + 2)
    -- Take a * z2 - b * z1 + c * z0 and get
    -- s(k + 3) = a * s(k + 2) - b * s(k + 1) + c * s(k) = a * z2 - b * z1 + c * z0.
    use a * z2 - b * z1 + c * z0
    simp [hs_rec, hz0, hz1, hz2]
  exact h n