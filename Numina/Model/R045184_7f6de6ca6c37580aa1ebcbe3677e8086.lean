import Mathlib

theorem number_theory_4516_1 {a b : ℕ} (hab : a.Coprime b) (ha : 0 < a) (hb : 0 < b) {n : ℕ} (hn : 0 < n):
    (a^n).Coprime (b^n) := by
  have hanpos : 0 < a^n := Nat.pow_pos ha
  have hbnpos : 0 < b^n := Nat.pow_pos hb
  
  rwa [← Nat.disjoint_primeFactors ha.ne' hb.ne',
    ← Nat.primeFactors_pow a hn.ne',
    ← Nat.primeFactors_pow b hn.ne',
    Nat.disjoint_primeFactors hanpos.ne' hbnpos.ne'] at hab

theorem number_theory_4516_2 {a b n : ℕ} (ha : 0 < a) (hb : 0 < b) (hn : 0 < n) (hab : a^n ∣ b^n) : a ∣ b := by
  have h2 : a ^ n ∣ b ^ n := hab 
  have h3 : a ∣ b := by
    apply (Nat.pow_dvd_pow_iff (by linarith)).mp at h2 
    all_goals tauto
  exact h3