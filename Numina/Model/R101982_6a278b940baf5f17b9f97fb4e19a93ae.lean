import Mathlib

theorem algebra_198852 {x : ℕ} (hx : x ∈ Finset.Icc 100 999) (h5 : 5 ∣ x) (h : ∃ n, x = n^3 + n^2) :
    x = 150 ∨ x = 810 := by 
  rw [Finset.mem_Icc] at hx
  rcases h with ⟨n, hn⟩
  rcases hx with ⟨hx1, hx2⟩
  have h1 : n^3 + n^2 ≥ 100 := by 
    linarith
  have h2 : n^3 + n^2 ≤ 999 := by 
    linarith
  have h9 : n ≤ 31 := by
    by_contra h
    push_neg at h
    have h10 : n ≥ 10 := by linarith
    have h11 : n^3 + n^2 > 999 := by
      nlinarith [show n ≥ 10 by linarith]
    nlinarith
  interval_cases n <;> omega