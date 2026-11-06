import Mathlib


theorem number_theory_610730:
  ∑ᶠ i ∈ {n:ℕ | IsSquare (n^2-3000) ∧ 0 < n^2 - 3000}, i = 1872 := by
  have h1 : {n : ℕ | IsSquare (n ^ 2 - 3000) ∧ 0 < n ^ 2 - 3000} = 
      Finset.filter (fun n => IsSquare (n ^ 2 - 3000) ∧ 0 < n ^ 2 - 3000) (Finset.Icc 0 1501) := by
    ext n
    simp 
    intro h1 h2
    have h3 : n ^ 2 - 3000 > 0 := by
      omega
    rcases h1 with ⟨r, hr⟩
    have h5 : n ^ 2 = r ^ 2 + 3000 := by
      have eq2 : n ^ 2 = r * r + 3000 := by 
        omega -- using hr: n^2 - 3000 = r*r
      have eq3 : r * r = r ^ 2 := by 
        ring
      calc 
        n ^ 2 = r * r + 3000 := eq2
        _ = r ^ 2 + 3000 := by 
          rw [eq3]
    have h6 : n ≤ 1501 := by
      by_contra h
      push_neg at h 
      have h7 : r ≥ n := by 
        nlinarith [sq_nonneg (n - r : ℤ), sq_nonneg (r : ℤ)]
      nlinarith [sq_nonneg (n + r : ℤ), sq_nonneg (n - r : ℤ)]
    omega 
  rw [h1]
  rw [finsum_mem_coe_finset]
  native_decide