import Mathlib

theorem number_theory_293297 (n : ℕ) (hn : 3 ≤ n) (a : Finset.Icc 1 n → ℕ)
    (hcoprime : ∀ i j, i ≠ j → Nat.Coprime (a i) (a j))
    (hlcm : ∏ i, a i ∣ ∑ i, a i) :
    ∏ i, a i ∣ (∑ i, a i) ^ (n - 2) := by 
  have h_pos : n - 2 > 0 := by omega 
  have h2 : ∏ i, a i ∣ (∑ i, a i) ^ (n - 2) := by
    apply dvd_pow 
    exact hlcm 
    all_goals omega
  exact h2