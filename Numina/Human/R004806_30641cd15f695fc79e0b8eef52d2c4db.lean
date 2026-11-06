import Mathlib

open Finset
theorem algebra_358043 {a : ℕ → ℝ} (ha1 : a 1 = 1) (han : ∀ n, a (n + 1) - a n = n + 1) :
    ∑ i ∈ range 11, (1 / a (i + 1)) = 11 / 6 := by
  have h_a0: a 0 = 0 := by
    have h := han 0
    simp at h
    linarith
  have hs (n: ℕ): ∑ i ∈ range n, ((i + 1):ℝ) = ∑ i ∈ range n, (a (i + 1) - a i) := by
    apply sum_congr rfl
    intro x hx
    rw [han]

  have ha (n: ℕ): a n = ∑ i ∈ range (n + 1), i := by
    rw [eq_sum_range_sub a]
    simp [<-hs n, sum_add_distrib, sum_range_succ, h_a0]

  have ha' (n: ℕ): a n = n * (n + 1) / 2 := by
    simp [ha, sum_range_id, mul_comm]
    have h: 2 ∣ n * (n + 1) := Even.two_dvd (Nat.even_mul_succ_self n)
    rw [Nat.cast_div h (by simp)]
    simp

  have h_a_reciprocol (n: ℕ): (a (n + 1))⁻¹ = 2 *(1 / (n + 1) - 1 / (n + 2)) := by
    rw [ha' (n + 1), div_sub_div _ _ (by linarith) (by linarith)]
    field_simp
    nlinarith

  generalize hf: (λ(n: ℕ) => (n + 1:ℝ)⁻¹) = f

  have h_sum: ∑ i ∈ range 11, (1 / a (i + 1)) = 2 • ∑ i ∈ range 11, (f i - f (i + 1)) := by
    rw [smul_sum]
    apply sum_congr rfl
    intro x
    simp_intro hx
    simp [h_a_reciprocol, <-hf]
    nlinarith
  rw [h_sum, sum_range_sub', <-hf]
  ring
