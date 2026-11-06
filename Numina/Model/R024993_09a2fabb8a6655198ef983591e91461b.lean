import Mathlib

/- If $n$ is a three-digit odd number, and the sum of its digits does not exceed $16$, find the maximum possible value of $n$.

 -/
theorem number_theory_7125 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : Odd n)
    (h₂ : (Nat.digits 10 n).sum ≤ 16) :
    n ≤ 961 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₃, h₄⟩
  by_contra h
  push_neg at h
  have h5 : n > 961 := by linarith
  have h6 : n ≤ 999 := h₄
  interval_cases n <;> norm_num [Nat.odd_iff] at h₁ h₂
  <;> all_goals contradiction