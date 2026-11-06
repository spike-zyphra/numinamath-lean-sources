import Mathlib

/-let f(x) = x ^ 2 + 6 * x + 6. compute the greatest real x such that f^[5] (x) = 0-/

noncomputable def f (x: ℝ): ℝ := x ^ 2 + 6 * x + 6
theorem algebra_610806 {x: ℝ} (hx: f^[5] (x) = 0): x = 3 ^ ((1:ℝ) /32) - 3 ∨ x = -3 ^ ((1:ℝ) /32) - 3:= by
  have id: ∀ y: ℝ, ∀ k: ℕ, f^[k] (y - 3) = y ^ (2 ^ k) - 3 := by
    intro y k
    induction k with
    | zero => simp
    | succ k ih =>
      simp [Function.iterate_succ_apply']
      rw [ih]
      simp [f]
      rw [show y ^ 2 ^ (k + 1) = (y ^ 2 ^ k) ^ 2 by ring]
      ring
  set y:= x + 3 with hy
  replace hy: x = y - 3 := by simp [hy]
  specialize id y
  specialize id 5
  have o: f^[5] x = f^[5] (y - 3) := by
    simp [hy]
  rw [o] at hx
  rw [id] at hx
  replace hx: y ^ 32 = 3 := by rw [show 2 ^ 5 = 32 by norm_num] at hx; rw [show y ^ 32 = y ^ 32 - 0 by ring];  rw [← hx]; ring
  set t:= y / (3 ^ ((1:ℝ) /32)) with ht
  have t1: ((3: ℝ) ^ ((1:ℝ) /32)) ^ 32 = 3 := by rw [←Real.rpow_mul_natCast];simp;norm_num
  replace ht: y = t * 3 ^ ((1:ℝ) /32) := by rw [ht]; simp
  rw [ht] at hx
  rw [show (t * (3 ^ ((1: ℝ) / 32))) ^ 32 = (t ^ 32) * (3 ^ ((1:ℝ) / 32)) ^ 32 by ring] at hx
  rw [t1] at hx
  simp at hx
  by_cases l: 0 ≤ t
  . rw [pow_eq_one_iff_of_nonneg l] at hx
    simp [hx] at ht
    simp [ht] at hy
    left
    simp [hy]
    norm_num
  . simp at l
    set p:= -t with hp
    replace hp: t = -p := by simp [hp]
    simp [hp] at hx
    have o: (-p) ^ 32 = p ^ 32 := by
      rw [show (-p) ^ 32 = (-1) ^ 32 * p ^ 32 by ring]
      have i: (-1: ℝ) ^ 32 = 1 := by norm_num
      rw [i]
      simp
    rw [o] at hx
    replace l: 0 ≤ p := by linarith
    rw [pow_eq_one_iff_of_nonneg l] at hx
    simp [hx] at hp
    simp [hp] at ht
    simp [ht] at hy
    right
    simp [hy]
    norm_num