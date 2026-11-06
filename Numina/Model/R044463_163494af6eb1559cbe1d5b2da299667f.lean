import Mathlib

open Finset Nat

theorem algebra_610055 {bounded_pairs : Finset (ℤ × ℤ)}
    {mxn : ℕ} (hmxn : mxn = 45)
    (hbp : bounded_pairs = (Finset.Icc (-mxn : ℤ) mxn).product (Icc (-mxn : ℤ) mxn)) :
    #({p ∈ bounded_pairs |
      (p.1 ^ 2 + p.2 ^ 2 < 2019) ∧ (p.1 ^ 2 + (min p.1 p.2) = p.2 ^ 2 + (max p.1 p.2))}) = 127 := by

  rw [hmxn] at hbp
  rw [hbp]
  native_decide