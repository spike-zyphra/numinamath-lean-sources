import Mathlib

theorem number_theory_201037 (a p q : ℕ) (ha : a.Prime) (hp : p.Prime) (hq : q.Prime)
    (hpa : a < p) (h : a + p = q) : a = 2 := by
  by_cases h1 : a ≤ 2
  · interval_cases a <;> norm_num at ha hp hq hpa h ⊢ <;> norm_num [Nat.Prime] at ha hp hq <;> try { 
      have : q = 2 := by
        nlinarith
      omega
    } <;> try { contradiction }
    <;> try { norm_num at h; all_goals nlinarith }
    <;> try { tauto } 
    <;> try { try { contradiction } <;> omega }
    <;> try { try { norm_num at hp hq } <;> try { contradiction } <;> omega }
    <;> try { assumption } 
    <;> try { try { tauto } <;> try { contradiction } <;> try { omega } }
  · -- Case where $a > 2$, so $a$ must be odd and not prime
    have h1 : a > 2 := by omega
    have h3 : a % 2 = 1 := by
      by_contra h4
      push_neg at h4
      have h4' : a % 2 = 0 := by omega
      have h5 : ¬ a.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ a by omega) (by omega) (by omega)
      contradiction
    have h7 : p % 2 = 1 := by
      by_contra h8
      push_neg at h8
      have h8' : p % 2 = 0 := by omega
      have h9 : ¬ p.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by omega) (by omega)
      contradiction
    have hq2 : q % 2 = 0 := by
      have h1' : a % 2 = 1 := h3
      have h7' : p % 2 = 1 := h7
      have : q % 2 = (a + p) % 2 := by 
        rw [h]
      rw [this]
      simp [Nat.add_mod, h1', h7']
    have h10 : q > 2 := by
      nlinarith [hpa, h, show a ≥ 3 by omega, show p ≥ 4 by omega]
      <;> ring_nf
      <;> nlinarith
    have h11 : ¬ q.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega) (by omega) (by omega)
    contradiction
    all_goals nlinarith <;> try { contradiction } <;> try { tauto } <;> try { omega }