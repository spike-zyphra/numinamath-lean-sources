import Mathlib

theorem number_theory_300095 (n : ℕ) (h₀ : n ∈ Finset.Icc 1000 9999) (h₁ : 111 ∣ n)
    (h₂ : n / 111 = (Nat.digits 10 n).sum) :
    n = 2997 := by 
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₃, h₄⟩

  set k := n / 111 with hk
  have eq1 : n = 111 * k := by
    have h111 : 111 ∣ n := h₁
    -- Since 111 divides n, n = 111 * k where k = n / 111
    have h8 : n = 111 * k := by 
      have h9 : k = n / 111 := by 
        omega
      have eq2 : n = 111 * (n / 111) := by 
        omega
      rw [h9] at *
      all_goals omega
    exact h8

  have h5 : k = (Nat.digits 10 n).sum := by 
    omega

  have h6 : k ≥ 9 := by 
    omega

  have h7 : k ≤ 90 := by 
    omega 

  interval_cases k <;> norm_num [eq1, h5] at *
  <;> omega