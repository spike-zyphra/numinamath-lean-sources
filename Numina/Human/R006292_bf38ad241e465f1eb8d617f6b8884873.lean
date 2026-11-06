import Mathlib

open Finset

theorem number_theory_635582 (N M : ℕ) (hN : N > 0) (hM : M > 0)
  (x y : ℤ) (hx : x = ∑ i ∈ range N, 2 ^ i)
  (hy : y = ((3 ^ 3) ^ 3 / 3 ^ 8 + 10 ^ 10 / 10 ^ 8 - 72) ^ M - 2015 ^ 0) :
  (x + y) % 10 = (2 ^ N % 10 - 1) % 10 := by 
  -- use induction we can prove the genenral formula for x 
  have h1 : ∀ m, ∑ i ∈ range m, (2 : ℤ) ^ i = 2 ^ m - 1 := by
    intro m
    induction m with 
    | zero => 
      simp 
    | succ k ih =>
      rw [range_add_one, sum_insert, ih, pow_add]
      simp
      ring
      simp
  rw [hx, h1 N]
  simp at hy
  rw [hy]
  have eq1 : ((2 : ℤ) ^ N - 1 + (31 ^ M - 1)) % 10 = 
    (2 ^ N - 1) % 10 := by 
    refine
      Eq.symm
        ((fun a b c => (ZMod.intCast_eq_intCast_iff a b c).mp) (2 ^ N - 1)
          (2 ^ N - 1 + (31 ^ M - 1)) 10 ?_)
    norm_num
    have aux : (31 : ZMod 10) = 1 := by rfl
    rw [aux]
    simp
  rw [eq1]
  omega