import Mathlib

theorem number_theory_222336 :
    {n : ℕ | 10^5 ≤ n ∧ n < 10^6 ∧ 3 ≤ (n / 10^5) ∧ 3 * n = (n - 3 * 10 ^ 5) * 10 + 3} =
    {428571} := by
  ext n
  simp only [Nat.reducePow, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  . rintro ⟨h_nge, h_nlt, h_nfirstdig, h⟩
    have : 7 * n = 3 * 10 ^ 6 - 3 := by
      rify at h ⊢
      have : 3 * 100000 ≤ n := Nat.mul_le_of_le_div 100000 3 n h_nfirstdig
      rw [Nat.cast_sub this] at h
      ring_nf at h ⊢
      linarith
    rify at this ⊢
    ring_nf at this
    linarith only [this]
  . intro hn
    rw [hn]
    norm_num
