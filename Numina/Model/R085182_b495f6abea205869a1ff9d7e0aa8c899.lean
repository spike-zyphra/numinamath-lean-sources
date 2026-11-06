import Mathlib

theorem number_theory_293274 (n : ℕ) (hn : 3 ≤ n) (a : Fin n → ℕ)
    (hcoprime : ∀ i j, i ≠ j → Nat.Coprime (a i) (a j)) (hlcm : ∏ i, a i ∣ ∑ i, a i) :
    ∏ i, a i ∣ (∑ i, a i) ^ (n - 2) := by 
  have h1 : n - 2 ≥ 1 := by omega
  apply dvd_pow
  exact hlcm
  all_goals omega