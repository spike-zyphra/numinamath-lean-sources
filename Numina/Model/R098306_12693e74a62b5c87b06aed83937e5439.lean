import Mathlib

open Nat

/- g(n)=1 for all natural number n -/
def g_4606 := fun (_ : ℕ) => 1

lemma prod_g_eq_one (n : ℕ) : ∏ i ∈ Finset.Ico 1 n, (g_4606 i) = 1 := by
  induction n
  simp
  rename_i k hk
  cases k
  simp
  rename_i k
  rw [Finset.prod_Ico_succ_top]
  rw [hk]
  dsimp [g_4606]
  linarith

theorem number_theory_4606
    (n : ℕ)
    (a : ℕ → ℕ)
    (h₀ : 0 < n)
    (h₁ : ∀ i < n, 0 < a i)
    (h₂ : a n = (∏ i in Finset.Ico 1 n, (a i)!) - 1)
    (h₃ : a (n + 1) = ∏ i in Finset.Ico 1 n, (a i)!) :
    (a (n + 1))! = ∏ i in Finset.Ico 1 (n + 1), (a i)! := by

  have hge1 : ∏ i ∈ Finset.Ico 1 n, (a i) ! ≥ 1 := by
    nth_rw 2 [← prod_g_eq_one n]
    apply Finset.prod_le_prod
    intro i hi
    dsimp [g_4606]
    norm_num
    intro i hi
    dsimp [g_4606]
    simp at hi
    have h₁ := h₁ i hi.2
    have ha1 : 1 ≤ a i := by omega
    have ha2 := Nat.self_le_factorial (a i)
    apply le_trans ha1 ha2

  have h4 : a (n + 1) = a n + 1 := by
    rw [h₃, h₂]
    omega

  rw [h4]
  rw [Finset.prod_Ico_succ_top]
  simp [h₃, h₂]
  <;> simp [Nat.factorial] <;> omega
  all_goals linarith