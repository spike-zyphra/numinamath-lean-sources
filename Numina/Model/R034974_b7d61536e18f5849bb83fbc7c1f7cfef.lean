import Mathlib

open Finset

theorem number_theory_607693 (a b c d e : ℕ) : ¬ ∃ n : ℕ,
    ({a + b, a + c, a + d, a + e, b + c, b + d, b + e, c + d, c + e, d + e} : Multiset ℕ) =
    (Icc n (n + 9)).val := by
  rintro ⟨n, hn⟩
  have h4 : (a + b + a + c + a + d + a + e + b + c + b + d + b + e + c + d + c + e + d + e) = 10 * n + 45 := by
    have h2 : ( {a + b, a + c, a + d, a + e, b + c, b + d, b + e, c + d, c + e, d + e} : Multiset ℕ ) = (Icc n (n + 9)).val := hn
    have h5 : ( ({a + b, a + c, a + d, a + e, b + c, b + d, b + e, c + d, c + e, d + e} : Multiset ℕ) ).sum = ( ( (Icc n (n + 9)).val ) ).sum := by
      rw [h2]
    have h6 : ( ({a + b, a + c, a + d, a + e, b + c, b + d, b + e, c + d, c + e, d + e} : Multiset ℕ) ).sum = a + b + a + c + a + d + a + e + b + c + b + d + b + e + c + d + c + e + d + e := by
      simp [Finset.sum_insert, Finset.sum_singleton]
      <;> ring
    have h7 : ( ( (Icc n (n + 9)).val ) ).sum = 10 * n + 45 := by
      simp [Finset.sum_Icc_succ_top, add_assoc]
      <;> ring
    rw [h6] at h5
    rw [h7] at h5
    omega
  omega