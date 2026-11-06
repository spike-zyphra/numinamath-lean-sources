import Mathlib
open Set Nat 
noncomputable section

/-The Dyslexian alphabet consists of consonants and vowels. It so happens that a finite sequence of letters is a word in Dyslexian precisely if it alternates between consonants and vowels (it may begin with either). There are 4800 five-letter words in Dyslexian. How many letters are in the alphabet?-/
theorem combinatorics_611029 (c v : ℕ) (hc : c > 0) (hv : v > 0)
  (h_words : c * v * c * v * c + v * c * v * c * v = 4800) :
  c + v = 12 := by
  -- Simplify the word count formula.
  have h_cv_pos : c * v > 0 := mul_pos hc hv
  have h_formula : c * v * c * v * c + v * c * v * c * v = (c * v)^2 * (c + v) := by
    simp [pow_two]; ring
  -- Prove $(c * v)^2$ divides $4800$.
  have h_dvd : (c * v)^2 ∣ 4800 := by
    rw [h_formula] at h_words
    exists c + v
    exact h_words.symm
  -- Derive the approximate range for $c * v$.
  have h_ge_10: c * v > 10 := by
    by_contra h
    have h₁: c ≤ 10 := by nlinarith
    have h₂: v ≤ 10 := by nlinarith
    have h₃: (c * v)^2 * (c + v) ≤ 2000 := by nlinarith
    linarith
  have h_ge_10: c * v < 40  := by
    by_contra h
    have : (c * v)^2 ≥ 1600 := by nlinarith
    have : (c + v) ≤ 3 := by nlinarith
    have : c ≤ 3 := by nlinarith
    have : v ≤ 3 := by nlinarith
    have : c * v ≤ 9 := by nlinarith
    linarith
  -- Prove $c * v$ divides $40$.
  have h_cv_div_40 : c * v ∣ 40 := by
    have h_factor : 4800 = 3 * 40^2 := by norm_num
    rw [h_formula, h_factor] at h_words
    have h_div : (c * v)^2 ∣ 3 * 40^2 := by exists c + v; exact h_words.symm
    have h_div' : (c * v)^2 ∣ 40^2  := by
      have h_not_dvd_3: ¬ (c * v)^2 ∣ 3 := by exact Nat.not_dvd_of_pos_of_lt (by nlinarith) (by nlinarith)
      have h_not_3_dvd : ¬ 3 ∣ (c * v)^2 := by
        by_contra h
        have h₁: 3 ∣ (c * v) := by exact Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
        have : 9 ∣ (c * v)^2 := by
          have : 9 = 3 ^ 2 := by norm_num
          rw [this]
          exact (Nat.pow_dvd_pow_iff (by norm_num:2 ≠ 0)).mpr h₁
        have : 9 ∣ 4800 := by exact Nat.dvd_trans this h_dvd
        have : ¬ 9 ∣ 4800 := by norm_num
        contradiction
      have h_coprime : Nat.Coprime 3 ((c * v)^2) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h_not_3_dvd
      rw [Nat.coprime_comm] at h_coprime
      exact (Nat.Coprime.dvd_mul_left h_coprime).mp h_div
    exact (Nat.pow_dvd_pow_iff (by norm_num:2 ≠ 0)).mp h_div'
  -- Derive $c + v = 4800 / (c * v)^2$.
  have h_cv_sum : c + v = 4800 / (c * v)^2 := by
    rw [h_formula] at h_words
    have h_div : (c * v)^2 ∣ 4800 := by exists c + v; exact h_words.symm
    rw [← h_words, mul_comm, mul_div_cancel_right₀ _ (pow_ne_zero 2 (by nlinarith))]
  -- Enumerate divisors of $c * v$.
  have h_cv_20 : c * v = 20 := by
    have h_ds : divisors 40 = {1, 2, 4, 5, 8, 10, 20, 40} := by decide
    have h_c_ne: c ≠ 0 := by nlinarith
    have h_v_ne: v ≠ 0 := by nlinarith
    have h_div : c * v ∈ divisors 40 := mem_divisors.mpr ⟨h_cv_div_40, (by norm_num)⟩
    simp [h_ds] at h_div
    have : (c * v) ≥ 10 := by omega
    rcases h_div with h | h | h | h | h | h | h | h
    · simp [h] at h_words
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
  -- $c * v = 20$ implies $c + v = 12$.
  have h_c_v_12 : c + v = 12 := by
    rw [h_cv_sum, h_cv_20]; norm_num
  exact h_c_v_12
