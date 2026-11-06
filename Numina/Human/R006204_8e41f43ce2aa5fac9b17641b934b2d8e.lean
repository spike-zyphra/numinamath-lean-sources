import Mathlib

theorem useful_lemma_634638 (N m : ℕ) (hN : Odd N) (hm : 1 < m) (hsum : N > 0) :
    (∑ i in Finset.Icc 1 N, if Odd i then i else 0) % m = ((N + 1) / 2)^2 % m := by

  have l_sum_Icc_succ {n : ℕ} {f : ℕ → ℕ} :
      ∑ i ∈ Finset.Icc 1 (n + 1), f i = (∑ i ∈ Finset.Icc 1 n, f i) + f (n + 1) := by
    refine Finset.sum_Icc_succ_top ?_ f
    omega

  have h1 : ∀ n : ℕ, (∑ i in Finset.Icc 1 (n + 1), if Odd i then i else 0) = (((n + 1) + 1) / 2)^2 := by
    intro n
    induction' n with n ih
    · -- Base case
      simp
    · -- Inductive step
      rw [l_sum_Icc_succ]
      rw [ih]
      by_cases h : Odd (n + 2)
      . simp [h]
        have ⟨k, hk⟩ := h
        rw [hk]
        have h2kp1div2 : (2 * k + 1) / 2 = k := by omega
        have h2kp2div2 : (2 * k + 2) / 2 = k + 1 := by omega
        simp_rw [h2kp1div2, h2kp2div2]
        ring
      . simp [h]
        rw [Nat.not_odd_iff_even] at h
        have ⟨k, hk⟩ := h
        simp_rw [hk, ← mul_two]
        omega
  specialize h1 (N - 1)
  rw [Nat.sub_add_cancel hsum] at h1
  rw [h1]