import Mathlib

def f (m : ℕ) := if Even m then m / 2 else m + 1

theorem number_theory_266794 (a : ℕ → ℕ)
    (h₀ : a 0 = 3)
    (h₁ : ∀ i ∈ Finset.range 5, a (i + 1) = a i + f (a i) + 1) :
    a 4 = 43 := by
  have eq1 := h₁ 0 (Finset.mem_range.mpr (by norm_num))
  have eq2 := h₁ 1 (Finset.mem_range.mpr (by norm_num))
  have eq3 := h₁ 2 (Finset.mem_range.mpr (by norm_num))
  have eq4 := h₁ 3 (Finset.mem_range.mpr (by norm_num))
  have eq5 := h₁ 4 (Finset.mem_range.mpr (by norm_num))
  simp [Finset.mem_range] at eq1 eq2 eq3 eq4 eq5
  have ha1 : a 1 = 8 := by
    rw [h₀] at eq1
    simp [f, Nat.even_iff] at eq1 ⊢
    omega
  have ha2 : a 2 = 13 := by
    rw [show a 1 = 8 by exact ha1] at eq2
    simp [f, Nat.even_iff] at eq2 ⊢
    omega
  have ha3 : a 3 = 28 := by
    rw [show a 2 = 13 by exact ha2] at eq3
    simp [f, Nat.even_iff] at eq3 ⊢
    omega
  have ha4 : a 4 = 43 := by
    rw [show a 3 = 28 by exact ha3] at eq4
    simp [f, Nat.even_iff] at eq4 ⊢
    omega
  exact ha4