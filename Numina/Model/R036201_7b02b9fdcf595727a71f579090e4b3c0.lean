import Mathlib

theorem number_theory_1912 (p q r : ℕ) (hpqr : p.Prime ∧ q.Prime ∧ r.Prime)
    (h : p^2 = q^2 + r^2 + 5) :
    False := by
  rcases hpqr with ⟨hp, hq, hr⟩
  have eq1 : p ^ 2 % 4 = 0 ∨ p ^ 2 % 4 = 1 := by
    by_cases h2 : p > 2
    · -- p > 2, so p must be odd
      have h3 : p % 2 = 1 := by
        by_contra h4
        push_neg at h4
        have h4' : ¬p.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by omega) (by omega)
        tauto
      have eq2 : p % 4 = 1 ∨ p % 4 = 3 := by
        omega
      rcases eq2 with (h | h)
      · -- p % 4 = 1
        have h1 : p ^ 2 % 4 = 1 := by
          simp [Nat.pow_mod, h]
        exact Or.inr h1
      · -- p % 4 = 3
        have h1 : p ^ 2 % 4 = 1 := by
          simp [Nat.pow_mod, h]
        exact Or.inr h1
    · -- p ≤ 2
      have h4 : p = 2 := by
        interval_cases p <;> try tauto
      rw [h4]
      all_goals norm_num
  have eq2 : q ^ 2 % 4 = 0 ∨ q ^ 2 % 4 = 1 := by
    by_cases h2 : q > 2
    · -- q > 2, so q must be odd
      have h3 : q % 2 = 1 := by
        by_contra h4
        push_neg at h4
        have h4' : ¬q.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega) (by omega) (by omega)
        tauto
      have eq2 : q % 4 = 1 ∨ q % 4 = 3 := by
        omega
      rcases eq2 with (h | h)
      · -- q % 4 = 1
        have h1 : q ^ 2 % 4 = 1 := by
          simp [Nat.pow_mod, h]
        exact Or.inr h1
      · -- q % 4 = 3
        have h1 : q ^ 2 % 4 = 1 := by
          simp [Nat.pow_mod, h]
        exact Or.inr h1
    · -- q ≤ 2
      have h4 : q = 2 := by
        interval_cases q <;> try tauto
      rw [h4]
      all_goals norm_num
  have eq3 : r ^ 2 % 4 = 0 ∨ r ^ 2 % 4 = 1 := by
    by_cases h2 : r > 2
    · -- r > 2, so r must be odd
      have h3 : r % 2 = 1 := by
        by_contra h4
        push_neg at h4
        have h4' : ¬r.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ r by omega) (by omega) (by omega)
        tauto
      have eq2 : r % 4 = 1 ∨ r % 4 = 3 := by
        omega
      rcases eq2 with (h | h)
      · -- r % 4 = 1
        have h1 : r ^ 2 % 4 = 1 := by
          simp [Nat.pow_mod, h]
        exact Or.inr h1
      · -- r % 4 = 3
        have h1 : r ^ 2 % 4 = 1 := by
          simp [Nat.pow_mod, h]
        exact Or.inr h1
    · -- r ≤ 2
      have h4 : r = 2 := by
        interval_cases r <;> try tauto
      rw [h4]
      all_goals norm_num
  have eq4 : p ^ 2 % 4 = (q ^ 2 + r ^ 2 + 5) % 4 := by
    omega
  by_cases h1 : p ^ 2 % 4 = 0
  · -- p^2 ≡ 0 (mod 4)
    have hp2 : p ^ 2 % 4 = 0 := by
      omega
    have hp20 : p % 2 = 0 := by
      have h1 : p % 4 = 0 ∨ p % 4 = 2 := by
        have : p ^ 2 % 4 = 0 := hp2
        have : p % 4 = 0 ∨ p % 4 = 1 ∨ p % 4 = 2 ∨ p % 4 = 3 := by omega
        rcases this with (h | h | h | h) <;> simp [pow_two, Nat.mul_mod, h] at hp2 <;> tauto
      omega
    have hp2 : p = 2 := by
      by_cases h4 : p > 2
      · -- p > 2
        have hp3 : p % 2 = 0 := hp20
        have hp4 : ¬p.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by omega) (by omega)
        tauto
      · -- p ≤ 2
        interval_cases p <;> try tauto
    have hp2' : p ^ 2 = 4 := by
      nlinarith [hp2]
    have h' : q ^ 2 + r ^ 2 + 5 = 4 := by
      nlinarith [h, hp2']
    have h7 : q ≤ 2 := by
      nlinarith [show q ^ 2 ≤ q ^ 2 + r ^ 2 by nlinarith [show r ^ 2 ≥ 0 by nlinarith]]
    have h8 : r ≤ 2 := by
      nlinarith [show r ^ 2 ≤ q ^ 2 + r ^ 2 by nlinarith [show q ^ 2 ≥ 0 by nlinarith]]
    interval_cases q <;> interval_cases r
    <;> norm_num at h' hp2' h7 h8
  · -- p^2 ≡ 1 (mod 4)
    have hp21 : p ^ 2 % 4 = 1 := by
      omega
    have h21 : (q ^ 2 + r ^ 2) % 4 = 0 := by
      omega
    have h22 : q ^ 2 % 4 = 0 := by
      omega
    have h23 : r ^ 2 % 4 = 0 := by
      omega
    have h31 : q % 2 = 0 := by
      have h1 : q % 4 = 0 ∨ q % 4 = 2 := by
        have h3 : q ^ 2 % 4 = 0 := h22
        have : q % 4 = 0 ∨ q % 4 = 1 ∨ q % 4 = 2 ∨ q % 4 = 3 := by omega
        rcases this with (h | h | h | h) <;> simp [pow_two, Nat.mul_mod, h] at h3 <;> tauto
      omega
    have h32 : r % 2 = 0 := by
      have h1 : r % 4 = 0 ∨ r % 4 = 2 := by
        have h3 : r ^ 2 % 4 = 0 := h23
        have : r % 4 = 0 ∨ r % 4 = 1 ∨ r % 4 = 2 ∨ r % 4 = 3 := by omega
        rcases this with (h | h | h | h) <;> simp [pow_two, Nat.mul_mod, h] at h3 <;> tauto
      omega
    have h41 : q = 2 := by
      by_cases h4 : q > 2
      · -- q > 2
        have h14 : q % 2 = 0 := h31
        have h15 : ¬q.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega) (by omega) (by omega)
        tauto
      · -- q ≤ 2
        interval_cases q <;> try tauto
    have h42 : r = 2 := by
      by_cases h4 : r > 2
      · -- r > 2
        have h14 : r % 2 = 0 := h32
        have h15 : ¬r.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ r by omega) (by omega) (by omega)
        tauto
      · -- r ≤ 2
        interval_cases r <;> try tauto
    have h43 : p ^ 2 = 13 := by
      rw [h41, h42] at h
      nlinarith
    have h44 : p ≤ 3 := by
      nlinarith [show p ^ 2 ≤ 16 from by nlinarith]
    interval_cases p <;> try omega