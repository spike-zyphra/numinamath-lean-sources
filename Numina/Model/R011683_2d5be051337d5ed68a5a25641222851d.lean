import Mathlib

theorem number_theory_51876_1 :
    ∀ (a b c d : ℤ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hd : 0 < d),
    (∀ x : ℤ, 5 ∣ a * x ^ 3 + b * x ^ 2 + c * x + d) →
    (5 ∣ a ∧ 5 ∣ b ∧ 5 ∣ c ∧ 5 ∣ d) := by
  intro a b c d ha hb hc hd h
  have h0 : 5 ∣ a * (0:ℤ) ^ 3 + b * (0:ℤ) ^ 2 + c * (0:ℤ) + d := h 0
  have h1 : 5 ∣ a * (1:ℤ) ^ 3 + b * (1:ℤ) ^ 2 + c * (1:ℤ) + d := h 1
  have h2 : 5 ∣ a * (2:ℤ) ^ 3 + b * (2:ℤ) ^ 2 + c * (2:ℤ) + d := h 2
  have h3 : 5 ∣ a * (3:ℤ) ^ 3 + b * (3:ℤ) ^ 2 + c * (3:ℤ) + d := h 3
  have h4 : 5 ∣ a * (4:ℤ) ^ 3 + b * (4:ℤ) ^ 2 + c * (4:ℤ) + d := h 4
  norm_num at h0 h1 h2 h3 h4
  constructor
  · -- Show 5 ∣ a
    omega
  constructor
  · -- Show 5 ∣ b
    omega
  constructor
  · -- Show 5 ∣ c
    omega
  · -- Show 5 ∣ d
    omega

theorem negated_number_theory_51876_2 :
    ∀ (a b c d : ℤ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hd : 0 < d),
    (∀ x : ℤ, 7 ∣ a * x ^ 3 + b * x ^ 2 + c * x + d) →
    (7 ∣ a ∧ 7 ∣ b ∧ 7 ∣ c ∧ 7 ∣ d) := by
  intro a b c d ha hb hc hd h
  have h0 : 7 ∣ a * (0:ℤ) ^ 3 + b * (0:ℤ) ^ 2 + c * (0:ℤ) + d := h 0
  have h1 : 7 ∣ a * (1:ℤ) ^ 3 + b * (1:ℤ) ^ 2 + c * (1:ℤ) + d := h 1
  have h2 : 7 ∣ a * (2:ℤ) ^ 3 + b * (2:ℤ) ^ 2 + c * (2:ℤ) + d := h 2
  have h3 : 7 ∣ a * (3:ℤ) ^ 3 + b * (3:ℤ) ^ 2 + c * (3:ℤ) + d := h 3
  have h4 : 7 ∣ a * (4:ℤ) ^ 3 + b * (4:ℤ) ^ 2 + c * (4:ℤ) + d := h 4
  have h5 : 7 ∣ a * (5:ℤ) ^ 3 + b * (5:ℤ) ^ 2 + c * (5:ℤ) + d := h 5
  have h6 : 7 ∣ a * (6:ℤ) ^ 3 + b * (6:ℤ) ^ 2 + c * (6:ℤ) + d := h 6
  norm_num at h0 h1 h2 h3 h4 h5 h6
  constructor
  · -- Show 7 ∣ a
    omega
  constructor
  · -- Show 7 ∣ b
    omega
  constructor
  · -- Show 7 ∣ c
    omega
  · -- Show 7 ∣ d
    omega