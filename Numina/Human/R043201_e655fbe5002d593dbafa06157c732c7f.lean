import Mathlib

/- Exercise 3. Let $P(x)=x^{4}-x^{3}-3 x^{2}-x+1$. Show that there are infinitely many integers $n$ such that $P\left(3^{n}\right)$ is not prime. -/
theorem number_theory_292133 (P : ℤ → ℤ) (hP : P = fun x => x ^ 4 - x ^ 3 - 3 * x ^ 2 - x + 1) :
    {n | ¬ Prime (P (3 ^ n))}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  -- show that for any a there exists n > a such that P (3 ^ n) is not prime
  -- take n = 4 * (a + 1) + 1 > a
  use 4 * (a + 1) + 1
  refine ⟨?_, by omega⟩
  simp only [Set.mem_setOf_eq]
  simp_rw [pow_add, pow_mul, Int.reducePow]
  -- show that 5 divides P (3 ^ (4 * (a + 1) + 1)) = P (81 ^ (a + 1) * 3)
  have h5 : 5 ∣ P (81 ^ (a + 1) * 3) := by
    simp [hP, ←pow_mul, mul_pow]
    -- we have 81 = 1 (mod 5)
    -- and we get P (81 ^ (a + 1) * 3) = 0 (mod 5)
    rw [show (5 : ℤ) = (5 : ℕ) from rfl, ←ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    reduce_mod_char
    simp [one_pow]
    reduce_mod_char
  simp [←Int.natAbs_dvd_natAbs] at h5
  rw [Int.prime_iff_natAbs_prime]
  -- assume that P (81 ^ (a + 1) * 3) is a prime number
  -- from 5 ∣ P (81 ^ (a + 1) * 3) it follows that P (81 ^ (a + 1) * 3) = 5
  -- show that it is false
  contrapose! h5
  rw [Nat.prime_dvd_prime_iff_eq Nat.prime_five h5]
  zify
  -- it is enough to show that 5 < P (81 ^ (a + 1) * 3)
  suffices 5 < P (81 ^ (a + 1) * 3) by
    rw [abs_of_nonneg (by linarith)]
    linarith
  -- we have 5 < P x for all x ≥ 3
  have h {x} (hx : 3 ≤ x) : P x > 5 := calc
    P x ≥ 2 * x ^ 3 - 3 * x ^ 2 - x + 1 := by
        simp only [hP, ge_iff_le, add_le_add_iff_right, tsub_le_iff_right, sub_add_cancel]
        rw [show 2 * x ^ 3 = 3 * x ^ 3 - x ^ 3 by ring, show x ^ 4 = x * x ^ 3 by ring]
        simp only [tsub_le_iff_right, sub_add_cancel]
        apply mul_le_mul hx (le_refl _) _ (by linarith)
        apply pow_nonneg (by linarith)
    _ ≥ 3 * x ^ 2 - x + 1 := by simp; nlinarith
    _ ≥ 8 * x + 1 := by nlinarith
    _ > 5 := by linarith
  apply h
  -- 3 ≤ 81 ^ (a + 1) * 3 so P (81 ^ (a + 1) * 3) ≠ 5
  simp only [Nat.ofNat_pos, le_mul_iff_one_le_left]
  exact one_le_pow₀ (by norm_num)