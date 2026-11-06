import Mathlib

open Finset

lemma lemma_1 {d b c : ℤ} {k : ℕ} (a : ℕ → ℤ) (hdb : d ∣ b - c) :
    d ∣ ∑ i ∈ range (k+1), (a i * b ^ i) ↔ d ∣ ∑ i ∈ range (k+1), (a i * c ^ i) := by
  have h1 : ∀ i : ℕ, d ∣ (b ^ i - c ^ i) := by
    intro i
    induction i with
    | zero =>
      simp
    | succ i ih =>
      have h4 : d ∣ (b ^ (i + 1) - c ^ (i + 1)) := by
        have h5 : b ^ (i + 1) - c ^ (i + 1) = b * (b ^ i) - c * (c ^ i) := by ring
        rw [h5]
        have h7 : d ∣ (b - c) * (b ^ i) := by
          exact dvd_mul_of_dvd_left hdb (b ^ i)
        have h8 : d ∣ c * (b ^ i - c ^ i) := by
          exact dvd_mul_of_dvd_right ih c
        have h9 : d ∣ ( (b - c) * (b ^ i) + c * (b ^ i - c ^ i) ) := by
          exact Int.dvd_add h7 h8
        have h10 : (b * (b ^ i) - c * (c ^ i)) = ( (b - c) * (b ^ i) + c * (b ^ i - c ^ i) ) := by
          ring
        rw [h10]
        exact h9
      exact h4
  have h3 : d ∣ (∑ i in range (k + 1), a i * b ^ i - ∑ i in range (k + 1), a i * c ^ i) := by
    have h4 : ∑ i in range (k + 1), a i * b ^ i - ∑ i in range (k + 1), a i * c ^ i = ∑ i in range (k + 1), (a i * b ^ i - a i * c ^ i) := by
      rw [Finset.sum_sub_distrib]
    rw [h4]
    have h5 : ∀ i : ℕ, d ∣ (a i * b ^ i - a i * c ^ i) := by
      intro i
      have h8 : d ∣ (b ^ i - c ^ i) := h1 i
      have h7 : d ∣ (a i * (b ^ i - c ^ i)) := by
        exact dvd_mul_of_dvd_right h8 (a i)
      have h10 : a i * b ^ i - a i * c ^ i = a i * (b ^ i - c ^ i) := by
        ring
      rw [h10]
      exact h7
    have h9 : d ∣ ∑ i in range (k + 1), (a i * b ^ i - a i * c ^ i) := by
      apply Finset.dvd_sum
      intro i hi
      exact h5 i
    exact h9
  constructor
  ·
    intro h
    have h10 : d ∣ ∑ i in range (k + 1), a i * c ^ i := by
      have h11 : d ∣ (∑ i in range (k + 1), a i * b ^ i - (∑ i in range (k + 1), a i * b ^ i - ∑ i in range (k + 1), a i * c ^ i)) := by
        exact Int.dvd_sub h (show d ∣ (∑ i in range (k + 1), a i * b ^ i - ∑ i in range (k + 1), a i * c ^ i) by exact h3)
      have h12 : (∑ i in range (k + 1), a i * b ^ i - (∑ i in range (k + 1), a i * b ^ i - ∑ i in range (k + 1), a i * c ^ i)) = ∑ i in range (k + 1), a i * c ^ i := by
        ring
      rw [h12] at h11
      exact h11
    exact h10
  ·
    intro h
    have h10 : d ∣ ∑ i in range (k + 1), a i * b ^ i := by
      have h11 : d ∣ (∑ i in range (k + 1), a i * c ^ i + (∑ i in range (k + 1), a i * b ^ i - ∑ i in range (k + 1), a i * c ^ i)) := by
        exact Int.dvd_add h (show d ∣ (∑ i in range (k + 1), a i * b ^ i - ∑ i in range (k + 1), a i * c ^ i) by exact h3)
      have h12 : (∑ i in range (k + 1), a i * c ^ i + (∑ i in range (k + 1), a i * b ^ i - ∑ i in range (k + 1), a i * c ^ i)) = ∑ i in range (k + 1), a i * b ^ i := by
        ring
      rw [h12] at h11
      exact h11
    exact h10


theorem number_theory_4742 {k : ℕ} {d b : ℤ} {a : ℕ → ℤ} (hdb : d ∣ (b+1)):
    d ∣ ∑ i ∈ range (k+1), (a i * b ^ i) ↔ d ∣ ∑ i ∈ range (k+1), (-1)^i * a i := by

  have h1 : d ∣ b - (-1) := by
    have h2 : b - (-1) = b + 1 := by ring
    rw [h2] at *
    exact hdb

  have h3 : d ∣ ∑ i ∈ range (k+1), (a i * b ^ i) ↔ d ∣ ∑ i ∈ range (k+1), (a i * (-1 : ℤ) ^ i) := by
    apply lemma_1 a h1

  have h5 : ∑ i ∈ range (k+1), ((-1)^i * a i) = ∑ i ∈ range (k+1), (a i * (-1 : ℤ) ^ i) := by
    apply Finset.sum_congr
    · rfl
    · intro i hi
      ring

  rw [h5] at *
  exact h3